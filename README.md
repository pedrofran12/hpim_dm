# Dissector for HPIM-DM multicast routing protocol

This branch stores the dissectors to interpret HPIM-DM control packets using Wireshark.

Initially we have coded HPIM-DM control packets using a JSON format. Then we transitioned to a binary format. In this branch there are plugins and capture examples for both formats.

### Files

- [hpim-dm_binary.lua](hpim-dm_binary.lua) - plugin to dissect HPIM-DM control packets on binary format.
- [hpim-dm_json.lua](hpim-dm_json.lua) - plugin to dissect HPIM-DM control packets on JSON format. This plugin requires the installation of `cjson` to work.
- [hpim-dm_binary_capture.pcap](hpim-dm_binary_capture.pcap) - capture example of HPIM-DM control packets in binary format.
- [hpim-dm_json_capture.pcap](hpim-dm_json_capture.pcap) - capture example of HPIM-DM control packets in JSON format.

### Installation

* Copy and paste .lua plugin to Wireshark's plugins folder (check at wireshark: Help -> About Wireshark -> Folders -> Personal or Global Plugins).
* Open Wireshark, reload lua plugins (Analyze -> Reload Lua Plugins) and check if the new plugin is enabled (Analyze -> Enabled Protocols).
* Open a Wireshark capture (.pcap) and the new plugin will dissect HPIM-DM packets.


### References:

[Wireshark plugins folder](https://osqa-ask.wireshark.org/questions/39759/wireshark-not-loading-lua-plugins-from-usrsharewiresharkplugins)

[Lua examples](https://wiki.wireshark.org/Lua/Examples)
