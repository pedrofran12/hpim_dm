cd hpim_dm
#pip-3.2 install --index-url=https://pypi.python.org/simple/ -r requirements.txt

tcpdump -i eth0 -w /hosthome/Desktop/test_newproto/test_assert/TestResults/Router1_Source.pcap &
tcpdump -i eth1 -w /hosthome/Desktop/test_newproto/test_assert/TestResults/Router1_Router2.pcap &
tcpdump -i eth2 -w /hosthome/Desktop/test_newproto/test_assert/TestResults/Router1_Router3.pcap &
tcpdump -i eth3 -w /hosthome/Desktop/test_newproto/test_assert/TestResults/Router1_Router4.pcap &


python3 Run.py -stop
python3 Run.py -start
python3 Run.py -aiigmp eth0
python3 Run.py -aiigmp eth1
python3 Run.py -aiigmp eth2
python3 Run.py -aiigmp eth3
python3 Run.py -ai eth0
python3 Run.py -ai eth1
python3 Run.py -ai eth2
python3 Run.py -ai eth3
python3 Run.py -v
