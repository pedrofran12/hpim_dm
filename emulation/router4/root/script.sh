cd hpim_dm
#pip-3.2 install --index-url=https://pypi.python.org/simple/ -r requirements.txt

python3 Run.py -stop
python3 Run.py -start
python3 Run.py -t R4 10.5.5.7
python3 Run.py -aiigmp eth0
python3 Run.py -aimld eth0
python3 Run.py -aiigmp eth1
python3 Run.py -aimld eth1
python3 Run.py -ai eth0
python3 Run.py -6 -ai eth0
python3 Run.py -ai eth1
python3 Run.py -6 -ai eth1
python3 Run.py -v
