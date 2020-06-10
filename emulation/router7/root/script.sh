cd hpim_dm


tcpdump -i eth0 -w /hosthome/Desktop/test_newproto/test_sync/TestResults/Router7_Router5.pcap &
tcpdump -i eth1 -w /hosthome/Desktop/test_newproto/test_sync/TestResults/Router7_Client0.pcap &
tcpdump -i eth2 -w /hosthome/Desktop/test_newproto/test_sync/TestResults/Router7_Router2.pcap &


python3 Run.py -stop
python3 Run.py -start
python3 Run.py -aiigmp eth0
python3 Run.py -aimld eth0
python3 Run.py -aiigmp eth1
python3 Run.py -aimld eth1
python3 Run.py -aiigmp eth2
python3 Run.py -aimld eth2
python3 Run.py -ai eth0
python3 Run.py -6 -ai eth0
python3 Run.py -ai eth1
python3 Run.py -6 -ai eth1
python3 Run.py -ai eth2
python3 Run.py -6 -ai eth2
python3 Run.py -v
