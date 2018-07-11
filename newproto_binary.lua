----------------------------------------
-- script-name: dns_dissector.lua
--
-- author: Hadriel Kaplan <hadrielk at yahoo dot com>
-- Copyright (c) 2014, Hadriel Kaplan
-- This code is in the Public Domain, or the BSD (3 clause) license if Public Domain does not apply
-- in your country.
--
-- Version: 2.1
--
-- Changes since 2.0:
--   * fixed a bug with default settings
--   * added ability for command-line to overide defaults
--
-- Changes since 1.0:
--   * made it use the new ProtoExpert class model for expert info
--   * add a protocol column with the proto name
--   * added heuristic dissector support
--   * added preferences settings
--   * removed byteArray2String(), and uses the new ByteArray:raw() method instead
--
-- BACKGROUND:
-- This is an example Lua script for a protocol dissector. The purpose of this script is two-fold:
--   * To provide a reference tutorial for others writing Wireshark dissectors in Lua
--   * To test various functions being called in various ways, so this script can be used in the test-suites
-- I've tried to meet both of those goals, but it wasn't easy. No doubt some folks will wonder why some
-- functions are called some way, or differently than previous invocations of the same function. I'm trying to
-- to show both that it can be done numerous ways, but also I'm trying to test those numerous ways, and my more
-- immediate need is for test coverage rather than tutorial guide. (the Lua API is sorely lacking in test scripts)
--
-- OVERVIEW:
-- This script creates an elementary dissector for DNS. It's neither comprehensive nor error-free with regards
-- to the DNS protocol. That's OK. The goal isn't to fully dissect DNS properly - Wireshark already has a good
-- DNS dissector built-in. We don't need another one. We also have other example Lua scripts, but I don't think
-- they do a good job of explaining things, and the nice thing about this one is getting capture files to
-- run it against is trivial. (plus I uploaded one)
--
-- HOW TO RUN THIS SCRIPT:
-- Wireshark and Tshark support multiple ways of loading Lua scripts: through a dofile() call in init.lua,
-- through the file being in either the global or personal plugins directories, or via the command line.
-- See the Wireshark USer's Guide chapter on Lua (http://www.wireshark.org/docs/wsug_html_chunked/wsluarm.html).
-- Once the script is loaded, it creates a new protocol named "MyDNS" (or "MYDNS" in some places).  If you have
-- a capture file with DNS packets in it, simply select one in the Packet List pane, right-click on it, and
-- select "Decode As ...", and then in the dialog box that shows up scroll down the list of protocols to one
-- called "MYDNS", select that and click the "ok" or "apply" button.  Voila`, you're now decoding DNS packets
-- using the simplistic dissector in this script.  Another way is to download the capture file made for
-- this script, and open that - since the DNS packets in it use UDP port 65333 (instead of the default 53),
-- and since the MyDNS protocol in this script has been set to automatically decode UDP port 65333, it will
-- automagically do it without doing "Decode As ...".
--
----------------------------------------
-- do not modify this table
local debug_level = {
    DISABLED = 0,
    LEVEL_1  = 1,
    LEVEL_2  = 2
}

-- set this DEBUG to debug_level.LEVEL_1 to enable printing debug_level info
-- set it to debug_level.LEVEL_2 to enable really verbose printing
-- note: this will be overridden by user's preference settings
local DEBUG = debug_level.LEVEL_1

local default_settings =
{
    debug_level  = DEBUG,
    proto         = 103,
    heur_enabled = false,
}

-- for testing purposes, we want to be able to pass in changes to the defaults
-- from the command line; because you can't set lua preferences from the command
-- line using the '-o' switch (the preferences don't exist until this script is
-- loaded, so the command line thinks they're invalid preferences being set)
-- so we pass them in as command arguments insetad, and handle it here:
local args={...} -- get passed-in args
if args and #args > 0 then
    for _, arg in ipairs(args) do
        local name, value = arg:match("(.+)=(.+)")
        if name and value then
            if tonumber(value) then
                value = tonumber(value)
            elseif value == "true" or value == "TRUE" then
                value = true
            elseif value == "false" or value == "FALSE" then
                value = false
            elseif value == "DISABLED" then
                value = debug_level.DISABLED
            elseif value == "LEVEL_1" then
                value = debug_level.LEVEL_1
            elseif value == "LEVEL_2" then
                value = debug_level.LEVEL_2
            else
                error("invalid commandline argument value")
            end
        else
            error("invalid commandline argument syntax")
        end

        default_settings[name] = value
    end
end

local dprint = function() end
local dprint2 = function() end
local function reset_debug_level()
    if default_settings.debug_level > debug_level.DISABLED then
        dprint = function(...)
            print(table.concat({"Lua:", ...}," "))
        end

        if default_settings.debug_level > debug_level.LEVEL_1 then
            dprint2 = dprint
        end
    end
end

-- call it now
reset_debug_level()

dprint2("Wireshark version = ", get_version())
dprint2("Lua version = ", _VERSION)

----------------------------------------
-- Unfortunately, the older Wireshark/Tshark versions have bugs, and part of the point
-- of this script is to test those bugs are now fixed.  So we need to check the version
-- end error out if it's too old.
local major, minor, micro = get_version():match("(%d+)%.(%d+)%.(%d+)")
if major and tonumber(major) <= 1 and ((tonumber(minor) <= 10) or (tonumber(minor) == 11 and tonumber(micro) < 3)) then
        error(  "Sorry, but your Wireshark/Tshark version ("..get_version()..") is too old for this script!\n"..
                "This script needs Wireshark/Tshark version 1.11.3 or higher.\n" )
end

-- more sanity checking
-- verify we have the ProtoExpert class in wireshark, as that's the newest thing this file uses
assert(ProtoExpert.new, "Wireshark does not have the ProtoExpert class, so it's too old - get the latest 1.11.3 or higher")

----------------------------------------


----------------------------------------
-- creates a Proto object, but doesn't register it yet
local dns = Proto("sfmr","New Multicast Protocol")

----------------------------------------
local pf_boot_time = ProtoField.new("Boot Time", "sfmr.boot_time", ftypes.UINT32)
local pf_tree_source = ProtoField.new("Source", "sfmr.options.tree_source", ftypes.IPv4)
local pf_tree_group = ProtoField.new("Group", "sfmr.options.tree_group", ftypes.IPv4)
local pf_hello_holdtime = ProtoField.new("Holdtime", "sfmr.options.hello_holdtime", ftypes.UINT16)
local pf_assert_metric = ProtoField.new("Metric", "sfmr.options.assert_metric", ftypes.UINT32)
local pf_assert_metric_preference = ProtoField.new("Metric Preference", "sfmr.options.assert_metric_preference", ftypes.UINT32)
local pf_neighbor_boot_time = ProtoField.new("Neighbor Boot Time", "sfmr.options.neighbor_boot_time", ftypes.UINT32)
local pf_sequence_number = ProtoField.new("SequenceNumber", "sfmr.options.sequence_number", ftypes.UINT32)
local pf_my_snapshot_sequence_number = ProtoField.new("My Snapshot Sequence Number", "sfmr.options.my_snapshot_sequence_number", ftypes.UINT32)
local pf_neighbor_snapshot_sequence_number = ProtoField.new("Neighbor Snapshot Sequence Number", "sfmr.options.neighbor_snapshot_sequence_number", ftypes.UINT32)
local pf_checkpoint_sequence_number = ProtoField.new("Checkpoint Sequence Number", "sfmr.options.checkpoint_sequence_number", ftypes.UINT32)

packet_type = {
  [0] = "HELLO", 
  [1] = "SYNC",
  [2] = "I_AM_UPSTREAM", 
  [3] = "I_AM_NO_LONGER_UPSTREAM",
  [4] = "INTEREST",
  [5] = "NO_INTEREST",
  [6] = "ACK",
}

-- within the flags field, we want to parse/show the bits separately
-- note the "base" argument becomes the size of the bitmask'ed field when ftypes.BOOLEAN is used
-- the "mask" argument is which bits we want to use for this field (e.g., base=16 and mask=0x8000 means we want the top bit of a 16-bit field)
-- again the following shows different ways of doing the same thing basically
local pf_version                    = ProtoField.new   ("Version", "sfmr.version", ftypes.UINT8, nil, base.DEC, 0xF0)
local pf_type                       = ProtoField.new   ("Type", "sfmr.type", ftypes.UINT8, packet_type, base.DEC, 0x0F)
local pf_master_flag                = ProtoField.new   ("Master flag", "sfmr.options.master_flag", ftypes.BOOLEAN, nil, 32, 0x080000000)
local pf_more_flag                  = ProtoField.new   ("More flag", "sfmr.options.more_flag", ftypes.BOOLEAN, nil, 32, 0x040000000)
local pf_sync_sequence_number       = ProtoField.new   ("Sync Sequence Number", "sfmr.options.sync_sequence_number", ftypes.UINT32, nil, base.DEC, 0x3FFFFFFF)
local pf_flag_opcode                = ProtoField.new   ("Opcode", "mydns.flags.opcode", ftypes.UINT16, nil, base.DEC, 0x7800, "operation code")

----------------------------------------
-- this actually registers the ProtoFields above, into our new Protocol
-- in a real script I wouldn't do it this way; I'd build a table of fields programmatically
-- and then set dns.fields to it, so as to avoid forgetting a field

dns.fields = {pf_version, pf_type, pf_boot_time, pf_tree_source, pf_tree_group, pf_assert_metric,
      pf_assert_metric_preference, pf_hello_holdtime,
      pf_sequence_number, pf_my_snapshot_sequence_number,
      pf_neighbor_snapshot_sequence_number, pf_sync_sequence_number, pf_master_flag,
      pf_more_flag, pf_neighbor_boot_time, pf_checkpoint_sequence_number}



--------------------------------------------------------------------------------
-- preferences handling stuff
--------------------------------------------------------------------------------

-- a "enum" table for our enum pref, as required by Pref.enum()
-- having the "index" number makes ZERO sense, and is completely illogical
-- but it's what the code has expected it to be for a long time. Ugh.
local debug_pref_enum = {
    { 1,  "Disabled", debug_level.DISABLED },
    { 2,  "Level 1",  debug_level.LEVEL_1  },
    { 3,  "Level 2",  debug_level.LEVEL_2  },
}

dns.prefs.debug = Pref.enum("Debug", default_settings.debug_level,
                            "The debug printing level", debug_pref_enum)

dns.prefs.port  = Pref.uint("Port number", default_settings.port,
                            "The UDP port number for MyDNS")

dns.prefs.heur  = Pref.bool("Heuristic enabled", default_settings.heur_enabled,
                            "Whether heuristic dissection is enabled or not")

----------------------------------------
-- a function for handling prefs being changed
function dns.prefs_changed()
    dprint2("prefs_changed called")

    default_settings.debug_level  = dns.prefs.debug
    reset_debug_level()

    default_settings.heur_enabled = dns.prefs.heur

    if default_settings.port ~= dns.prefs.port then
        -- remove old one, if not 0
        if default_settings.port ~= 0 then
            dprint2("removing MyDNS from port",default_settings.port)
            DissectorTable.get("udp.port"):remove(default_settings.port, dns)
        end
        -- set our new default
        default_settings.port = dns.prefs.port
        -- add new one, if not 0
        if default_settings.port ~= 0 then
            dprint2("adding MyDNS to port",default_settings.port)
            DissectorTable.get("udp.port"):add(default_settings.port, dns)
        end
    end

end

dprint2("SFMR Prefs registered")


----------------------------------------
---- some constants for later use ----
-- the DNS header size
local DNS_HDR_LEN = 12

-- the smallest possible DNS query field size
-- has to be at least a label length octet, label character, label null terminator, 2-bytes type and 2-bytes class
local MIN_QUERY_LEN = 7

----------------------------------------



----------------------------------------
-- The following creates the callback function for the dissector.
-- It's the same as doing "dns.dissector = function (tvbuf,pkt,root)"
-- The 'tvbuf' is a Tvb object, 'pktinfo' is a Pinfo object, and 'root' is a TreeItem object.
-- Whenever Wireshark dissects a packet that our Proto is hooked into, it will call
-- this function and pass it these arguments for the packet it's dissecting.
function dns.dissector(tvbuf,pktinfo,root)
    dprint2("dns.dissector called")

    -- set the protocol column to show our protocol name
    pktinfo.cols.protocol:set("SFMR")

    -- We want to check that the packet size is rational during dissection, so let's get the length of the
    -- packet buffer (Tvb).
    -- Because DNS has no additional payload data other than itself, and it rides on UDP without padding,
    -- we can use tvb:len() or tvb:reported_len() here; but I prefer tvb:reported_length_remaining() as it's safer.
    local pktlen = tvbuf:reported_length_remaining()

    -- We start by adding our protocol to the dissection display tree.
    -- A call to tree:add() returns the child created, so we can add more "under" it using that return value.
    -- The second argument is how much of the buffer/packet this added tree item covers/represents - in this
    -- case (DNS protocol) that's the remainder of the packet.
    local tree = root:add(dns, tvbuf:range(0,pktlen))

    -- now let's check it's not too short
    if pktlen < DNS_HDR_LEN then
        -- since we're going to add this protocol to a specific UDP port, we're going to
        -- assume packets in this port are our protocol, so the packet being too short is an error
        -- the old way: tree:add_expert_info(PI_MALFORMED, PI_ERROR, "packet too short")
        -- the correct way now:
        tree:add_proto_expert_info(ef_too_short)
        dprint("packet length",pktlen,"too short")
        return
    end
    
    

    -- Now let's add our transaction id under our dns protocol tree we just created.
    -- The transaction id starts at offset 0, for 2 bytes length.
    tree:add(pf_boot_time, tvbuf:range(0,4))
    local version_and_type = tvbuf:range(4,1)
    local type = version_and_type:bitfield(4,4)
    tree:add(pf_version, tvbuf:range(4,1))
    tree:add(pf_type, tvbuf:range(4,1))
    local msg_type = packet_type[type]
    pktinfo.cols.info:set(msg_type)

 
    local pos = 8
    local queries_tree = tree:add("SFMR Options")
    if msg_type == "HELLO" then
      local pktlen_remaining = pktlen - pos
      
      while pktlen_remaining > 0 do
          local type = tvbuf:range(pos, 2):uint()
          local length = tvbuf:range(pos + 2, 2):uint()
          pos = pos + 4
          if type == 1 then
              queries_tree:add(pf_hello_holdtime, tvbuf:range(pos, length))
          elseif type == 2 then          
              queries_tree:add(pf_checkpoint_sequence_number, tvbuf(pos, length))
          end
          pos = pos + length
          pktlen_remaining = pktlen_remaining - (4 + length)
       end
    elseif msg_type == "INTEREST" or msg_type == "NO_INTEREST" or msg_type == "I_AM_NO_LONGER_UPSTREAM" then
      queries_tree:add(pf_tree_source, tvbuf:range(pos, 4))
      queries_tree:add(pf_tree_group, tvbuf:range(pos + 4, 4))
      queries_tree:add(pf_sequence_number, tvbuf:range(pos + 8, 4))      
    elseif msg_type == "ACK" then
      queries_tree:add(pf_tree_source, tvbuf:range(pos, 4))
      queries_tree:add(pf_tree_group, tvbuf:range(pos + 4, 4))   
      queries_tree:add(pf_neighbor_boot_time, tvbuf:range(pos + 8, 4))
      queries_tree:add(pf_sequence_number, tvbuf:range(pos + 12, 4))   
    elseif msg_type == "I_AM_UPSTREAM" then
      queries_tree:add(pf_tree_source, tvbuf:range(pos, 4))
      queries_tree:add(pf_tree_group, tvbuf:range(pos + 4, 4))   
      queries_tree:add(pf_sequence_number, tvbuf:range(pos + 8, 4))      
      queries_tree:add(pf_assert_metric_preference, tvbuf:range(pos + 12, 4))
      queries_tree:add(pf_assert_metric, tvbuf:range(pos + 16, 4))
   elseif msg_type == "SYNC" then
      queries_tree:add(pf_my_snapshot_sequence_number, tvbuf:range(pos, 4))
      queries_tree:add(pf_neighbor_snapshot_sequence_number, tvbuf:range(pos + 4, 4))
      queries_tree:add(pf_neighbor_boot_time, tvbuf:range(pos + 8, 4))      
      queries_tree:add(pf_sync_sequence_number, tvbuf:range(pos + 12, 4))
      queries_tree:add(pf_master_flag, tvbuf:range(pos + 12, 4))
      queries_tree:add(pf_more_flag, tvbuf:range(pos + 12, 4))
      pos = pos + 16
      local pktlen_remaining = pktlen - pos
      while pktlen_remaining > 0 do
            local tree_info = queries_tree:add("Tree (".. string.format("%s",tvbuf:range(pos, 4):ipv4()) .. "," .. string.format("%s",tvbuf:range(pos + 4, 4):ipv4()) .. ")")    
            tree_info:add(pf_tree_source, tvbuf:range(pos, 4))
            tree_info:add(pf_tree_group, tvbuf:range(pos + 4, 4))   
            tree_info:add(pf_assert_metric_preference, tvbuf:range(pos + 8, 4))
            tree_info:add(pf_assert_metric, tvbuf:range(pos + 12, 4))          
            pos = pos + 16
            pktlen_remaining = pktlen_remaining - 16
       end
   end
    -- tell wireshark how much of tvbuff we dissected
    return pos
end

----------------------------------------
-- we want to have our protocol dissection invoked for a specific IP Protocol Number,
-- so get the IP dissector table and add our protocol to it
DissectorTable.get("ip.proto"):add(default_settings.proto, dns)


-- We're done!
-- our protocol (Proto) gets automatically registered after this script finishes loading
----------------------------------------
