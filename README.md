# Dissector for new multicast routing protocol



### Installation

* Copy and paste .lua plugin to Wireshark's plugins folder (check at wireshark: Help -> About Wireshark -> Folders -> Personal or Global Plugins).
* Open Wireshark, reload lua plugins (Analyze -> Reload Lua Plugins) and check if the new plugin is enabled (Analyze -> Enabled Protocols).
* Open a Wireshark capture (.pcap) and the new plugin will dissect SFMR packets.


### References:

[Wireshark plugins folder](https://osqa-ask.wireshark.org/questions/39759/wireshark-not-loading-lua-plugins-from-usrsharewiresharkplugins)

[Lua examples](https://wiki.wireshark.org/Lua/Examples)
