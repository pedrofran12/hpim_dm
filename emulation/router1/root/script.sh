rm -rf MulticastRouting/
cp -rf /hosthome/Desktop/new_protocol2/ MulticastRouting/
cd MulticastRouting
#pip-3.2 install --index-url=https://pypi.python.org/simple/ -r requirements.txt

tcpdump -i eth0 -w /hosthome/Desktop/test_newproto/test_loop/TestResults/Router1_Source.pcap &
tcpdump -i eth1 -w /hosthome/Desktop/test_newproto/test_loop/TestResults/Router1_Router2.pcap &


python3 Run.py -stop
python3 Run.py -start
python3 Run.py -t R1 10.3.3.7
python3 Run.py -aiigmp eth0
python3 Run.py -aiigmp eth1
python3 Run.py -ai eth0
python3 Run.py -ai eth1
python3 Run.py -v