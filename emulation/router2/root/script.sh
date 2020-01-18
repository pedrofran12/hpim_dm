cd hpim_dm
#pip-3.2 install --index-url=https://pypi.python.org/simple/ -r requirements.txt

python3 Run.py -stop
python3 Run.py -start
python3 Run.py -t R2 10.0.0.5
python3 Run.py -aiigmp eth0
python3 Run.py -v
