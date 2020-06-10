cd hpim_dm

python3 Run.py -stop
python3 Run.py -start
python3 Run.py -t R5 10.3.3.7
python3 Run.py -aiigmp eth0
python3 Run.py -aiigmp eth1
python3 Run.py -aiigmp eth2
python3 Run.py -aimld eth0
python3 Run.py -aimld eth1
python3 Run.py -aimld eth2
python3 Run.py -ai eth0
python3 Run.py -ai eth1
python3 Run.py -ai eth2
python3 Run.py -ai eth0 -6
python3 Run.py -ai eth1 -6
python3 Run.py -ai eth2 -6
python3 Run.py -v
