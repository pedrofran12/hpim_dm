import socket
import time         
import sys
import fileinput
import os
import logging.handlers
import logging



#INICIALIZACAO
CLIENT_NAME = ""
SERVER_IP = ""

logger = logging.getLogger('tests')
logger.setLevel(logging.DEBUG)

CLIENT_PORT=12000

sock = socket.socket(socket.AF_INET,socket.SOCK_DGRAM)
sock.bind(('',12000))

#setlogger()



class RootFilter(logging.Filter):
	"""
	This is a filter which injects contextual information into the log.

	Rather than use actual contextual information, we just use random
	data in this demo.
	"""
	def __init__(self, router_name, tree=''):
		super().__init__()
		self.router_name = router_name

	def filter(self, record):
		record.routername = self.router_name
		record.tree = ''
		record.vif = ''
		record.interfacename = ''
		return True


def setLogger():
	global logger
	print("in setting logger")
	#logger.addHandler(logging.StreamHandler(sys.stdout))
	socketHandler = logging.handlers.SocketHandler(SERVER_IP, logging.handlers.DEFAULT_TCP_LOGGING_PORT)
	socketHandler.addFilter(RootFilter(CLIENT_NAME))
	logger.addHandler(socketHandler)


def sendTo_logger(message):
	global logger
	print("Message to server: " + message)
	logger.debug(message)


def settings(client_name, server_ip):
	global CLIENT_NAME
	CLIENT_NAME = client_name

	global SERVER_IP
	SERVER_IP = server_ip

	setLogger()


def stop_process():
	command = "python3 Run.py -stop"
	sendTo_logger(command)
	os.system(command)

	
def start_process():
	command = "python3 Run.py -start"
	sendTo_logger(command)
	os.system(command)


def restart_process():
	stop_process()
	start_process()


def enable_interface(interface):
	command = "python3 Run.py -ai " + interface
	sendTo_logger(command)
	os.system(command)


def remove_interface(interface):
	command = "python3 Run.py -ri " + interface
	sendTo_logger(command)
	os.system(command)
	

def tester():
	command = "python3 Run.py -t " + CLIENT_NAME + " " + SERVER_IP
	sendTo_logger(command)
	os.system(command)


def verbose():
	command = "python3 Run.py -v"
	sendTo_logger(command)
	os.system(command)


while True:
	(msg,addr) = sock.recvfrom(1024)
	msg = msg.decode('utf-8')
	cmds = msg.split()
	if cmds[0] == "set" and len(cmds) == 3:
		settings(cmds[1], cmds[2])
		continue
	elif cmds[0] == "start":
		start_process()
		continue
	elif cmds[0] == "stop":
		stop_process()
		continue
	elif cmds[0] == "restart":
		restart_process()
		continue
	elif cmds[0] == "t":
		tester()
		continue
	elif cmds[0] == "ai" and len(cmds) == 2:
		enable_interface(cmds[1])
		continue
	elif cmds[0] == "ri" and len(cmds) == 2:
		remove_interface(cmds[1])
		continue
	elif cmds[0] == "v":
		verbose()

sock.close()
