import yaml
from hpimdm.tree import hpim_globals
from hpimdm.igmp import igmp_globals
from hpimdm.mld import mld_globals
from hpimdm import Main


def parse_config_file(file_path):
    """
    Parse yaml file and set everything on protocol process accordingly
    """
    with open(file_path) as f:
        data = yaml.load(f, Loader=yaml.FullLoader)
        print(data)

        print(type(data.get("UnicastVRF", 254)))

        multicast_vrf = data.get("MulticastVRF", 0)
        hpim_globals.MULTICAST_TABLE_ID = multicast_vrf
        hpim_globals.UNICAST_TABLE_ID = data.get("UnicastVRF", 254)
        hpim_config = data.get("HPIM-DM", {})
        igmp_config = data.get("IGMP", {})
        mld_config = data.get("MLD", {})

        ##### HPIM config ######
        if "DefaultTimers" in hpim_config:
            hpim_globals.INITIAL_FLOOD_TIME = hpim_config["DefaultTimers"].get("INITIAL_FLOOD_TIME", hpim_globals.INITIAL_FLOOD_TIME)
            hpim_globals.HELLO_PERIOD = hpim_config["DefaultTimers"].get("HELLO_PERIOD", hpim_globals.HELLO_PERIOD)
            hpim_globals.SOURCE_LIFETIME = hpim_config["DefaultTimers"].get("SOURCE_LIFETIME", hpim_globals.SOURCE_LIFETIME)
            hpim_globals.MESSAGE_RETRANSMISSION_TIME = hpim_config["DefaultTimers"].get("MESSAGE_RETRANSMISSION_TIME", hpim_globals.MESSAGE_RETRANSMISSION_TIME)

        if "Settings" in hpim_config:
            hpim_globals.INITIAL_FLOOD_ENABLED = hpim_config["Settings"].get("INITIAL_FLOOD_ENABLED", hpim_globals.INITIAL_FLOOD_ENABLED)
            hpim_globals.SYNC_FRAGMENTATION_MSG = hpim_config["Settings"].get("SYNC_FRAGMENTATION_MSG", hpim_globals.SYNC_FRAGMENTATION_MSG)

        if "Interfaces" in hpim_config:
            interfaces = hpim_config["Interfaces"]  # type: dict

            for if_name, if_value in interfaces.items():
                if if_value.get("ipv4", False):
                    if_ipv4 = if_value["ipv4"]
                    if if_ipv4.get("enabled", False):
                        Main.add_hpim_interface(interface_name=if_name, ipv4=True, ipv6=False)

                        if if_ipv4.get("security", None):
                            interface_security = if_ipv4["security"]
                            if_sec_id = interface_security.get("identifier", 0)
                            if_sec_algorithm = interface_security.get("algorithm", "md5")
                            if_sec_key = interface_security.get("key", None)
                            if if_sec_key is not None:
                                Main.add_security_key(interface_name=if_name, security_identifier=if_sec_id,
                                                      hash_function=if_sec_algorithm, key=if_sec_key,
                                                      ipv4=True, ipv6=False)
                if if_value.get("ipv6", False):
                    if_ipv6 = if_value["ipv6"]
                    if if_ipv6.get("enabled", False):
                        Main.add_hpim_interface(interface_name=if_name, ipv4=False, ipv6=True)

                        if if_ipv6.get("security", None):
                            interface_security = if_ipv6["security"]
                            if_sec_id = interface_security.get("identifier", 0)
                            if_sec_algorithm = interface_security.get("algorithm", "md5")
                            if_sec_key = interface_security.get("key", None)
                            if if_sec_key is not None:
                                Main.add_security_key(interface_name=if_name, security_identifier=if_sec_id,
                                                      hash_function=if_sec_algorithm, key=if_sec_key,
                                                      ipv4=False, ipv6=True)

        ##### IGMP config #######
        if "Settings" in igmp_config:
            igmp_globals.ROBUSTNESS_VARIABLE = igmp_config["Settings"].get("ROBUSTNESS_VARIABLE", igmp_globals.ROBUSTNESS_VARIABLE)
            igmp_globals.QUERY_INTERVAL = igmp_config["Settings"].get("QUERY_INTERVAL", igmp_globals.QUERY_INTERVAL)
            igmp_globals.QUERY_RESPONSE_INTERVAL = igmp_config["Settings"].get("QUERY_RESPONSE_INTERVAL", igmp_globals.QUERY_RESPONSE_INTERVAL)
            igmp_globals.MAX_RESPONSE_TIME_QUERY_RESPONSE_INTERVAL = igmp_config["Settings"].get("MAX_RESPONSE_TIME_QUERY_RESPONSE_INTERVAL", igmp_globals.QUERY_RESPONSE_INTERVAL*10)
            igmp_globals.GROUP_MEMBERSHIP_INTERVAL = igmp_config["Settings"].get("GROUP_MEMBERSHIP_INTERVAL", igmp_globals.ROBUSTNESS_VARIABLE * igmp_globals.QUERY_INTERVAL + igmp_globals.QUERY_RESPONSE_INTERVAL)
            igmp_globals.OTHER_QUERIER_PRESENT_INTERVAL = igmp_config["Settings"].get("OTHER_QUERIER_PRESENT_INTERVAL", igmp_globals.ROBUSTNESS_VARIABLE * igmp_globals.QUERY_INTERVAL + igmp_globals.QUERY_RESPONSE_INTERVAL / 2)
            igmp_globals.STARTUP_QUERY_INTERVAL = igmp_config["Settings"].get("STARTUP_QUERY_INTERVAL", igmp_globals.QUERY_INTERVAL / 4)
            igmp_globals.STARTUP_QUERY_COUNT = igmp_config["Settings"].get("STARTUP_QUERY_COUNT", igmp_globals.ROBUSTNESS_VARIABLE)
            igmp_globals.LAST_MEMBER_QUERY_INTERVAL = igmp_config["Settings"].get("LAST_MEMBER_QUERY_INTERVAL", igmp_globals.LAST_MEMBER_QUERY_INTERVAL)
            igmp_globals.MAX_RESPONSE_TIME_LAST_MEMBER_QUERY_INTERVAL = igmp_config["Settings"].get("LAST_MEMBER_QUERY_COUNT", igmp_globals.LAST_MEMBER_QUERY_INTERVAL * 10)
            igmp_globals.LAST_MEMBER_QUERY_COUNT = igmp_config["Settings"].get("LAST_MEMBER_QUERY_COUNT", igmp_globals.ROBUSTNESS_VARIABLE)
            igmp_globals.UNSOLICITED_REPORT_INTERVAL = igmp_config["Settings"].get("UNSOLICITED_REPORT_INTERVAL", igmp_globals.UNSOLICITED_REPORT_INTERVAL)
            igmp_globals.VERSION_1_ROUTER_PRESENT_TIMEOUT = igmp_config["Settings"].get("VERSION_1_ROUTER_PRESENT_TIMEOUT", igmp_globals.VERSION_1_ROUTER_PRESENT_TIMEOUT)

        if "Interfaces" in igmp_config:
            interfaces = igmp_config["Interfaces"]  # type: dict

            for if_name, if_value in interfaces.items():
                if if_value.get("enabled", False):
                    Main.add_membership_interface(interface_name=if_name, ipv4=True, ipv6=False)

        ##### MLD config #######
        if "Settings" in mld_config:
            mld_globals.ROBUSTNESS_VARIABLE = mld_config["Settings"].get("ROBUSTNESS_VARIABLE", mld_globals.ROBUSTNESS_VARIABLE)
            mld_globals.QUERY_INTERVAL = mld_config["Settings"].get("QUERY_INTERVAL", mld_globals.QUERY_INTERVAL)
            mld_globals.QUERY_RESPONSE_INTERVAL = mld_config["Settings"].get("QUERY_RESPONSE_INTERVAL", mld_globals.QUERY_RESPONSE_INTERVAL)
            mld_globals.MULTICAST_LISTENER_INTERVAL = mld_config["Settings"].get("MULTICAST_LISTENER_INTERVAL", (mld_globals.ROBUSTNESS_VARIABLE * mld_globals.QUERY_INTERVAL) + (mld_globals.QUERY_RESPONSE_INTERVAL))
            mld_globals.OTHER_QUERIER_PRESENT_INTERVAL = mld_config["Settings"].get("OTHER_QUERIER_PRESENT_INTERVAL", (mld_globals.ROBUSTNESS_VARIABLE * mld_globals.QUERY_INTERVAL) + 0.5 * mld_globals.QUERY_RESPONSE_INTERVAL)
            mld_globals.STARTUP_QUERY_INTERVAL = mld_config["Settings"].get("STARTUP_QUERY_INTERVAL", (1 / 4) * mld_globals.QUERY_INTERVAL)
            mld_globals.STARTUP_QUERY_COUNT = mld_config["Settings"].get("STARTUP_QUERY_COUNT", mld_globals.ROBUSTNESS_VARIABLE)
            mld_globals.LAST_LISTENER_QUERY_INTERVAL = mld_config["Settings"].get("LAST_LISTENER_QUERY_INTERVAL", mld_globals.LAST_LISTENER_QUERY_INTERVAL)
            mld_globals.LAST_LISTENER_QUERY_COUNT = mld_config["Settings"].get("LAST_LISTENER_QUERY_COUNT", mld_globals.ROBUSTNESS_VARIABLE)
            mld_globals.UNSOLICITED_REPORT_INTERVAL = mld_config["Settings"].get("UNSOLICITED_REPORT_INTERVAL", mld_globals.UNSOLICITED_REPORT_INTERVAL)

        if "Interfaces" in mld_config:
            interfaces = mld_config["Interfaces"]  # type: dict

            for if_name, if_value in interfaces.items():
                if if_value.get("enabled", False):
                    Main.add_membership_interface(interface_name=if_name, ipv4=False, ipv6=True)


def get_yaml_file():
    """
    Get configuration file from live protocol process
    """
    dict_file = {
        'MulticastVRF': hpim_globals.MULTICAST_TABLE_ID,
        'UnicastVRF': hpim_globals.UNICAST_TABLE_ID,
        'HPIM-DM': {
            "DefaultTimers": {
                "INITIAL_FLOOD_TIME": hpim_globals.INITIAL_FLOOD_TIME,
                "HELLO_PERIOD": hpim_globals.HELLO_PERIOD,
                "SOURCE_LIFETIME": hpim_globals.SOURCE_LIFETIME,
                "MESSAGE_RETRANSMISSION_TIME": hpim_globals.MESSAGE_RETRANSMISSION_TIME
            },
            "Settings": {
                "INITIAL_FLOOD_ENABLED": hpim_globals.INITIAL_FLOOD_ENABLED,
                "SYNC_FRAGMENTATION_MSG": hpim_globals.SYNC_FRAGMENTATION_MSG
            },
            "Interfaces": {},
        },
        'IGMP': {
            "Settings": {
                "ROBUSTNESS_VARIABLE": igmp_globals.ROBUSTNESS_VARIABLE,
                "QUERY_INTERVAL": igmp_globals.QUERY_INTERVAL,
                "QUERY_RESPONSE_INTERVAL": igmp_globals.QUERY_RESPONSE_INTERVAL,
                "MAX_RESPONSE_TIME_QUERY_RESPONSE_INTERVAL": igmp_globals.MAX_RESPONSE_TIME_QUERY_RESPONSE_INTERVAL,
                "GROUP_MEMBERSHIP_INTERVAL": igmp_globals.GROUP_MEMBERSHIP_INTERVAL,
                "OTHER_QUERIER_PRESENT_INTERVAL": igmp_globals.OTHER_QUERIER_PRESENT_INTERVAL,
                "STARTUP_QUERY_INTERVAL": igmp_globals.STARTUP_QUERY_INTERVAL,
                "STARTUP_QUERY_COUNT": igmp_globals.STARTUP_QUERY_COUNT,
                "LAST_MEMBER_QUERY_INTERVAL": igmp_globals.LAST_MEMBER_QUERY_INTERVAL,
                "MAX_RESPONSE_TIME_LAST_MEMBER_QUERY_INTERVAL": igmp_globals.MAX_RESPONSE_TIME_LAST_MEMBER_QUERY_INTERVAL,
                "LAST_MEMBER_QUERY_COUNT": igmp_globals.LAST_MEMBER_QUERY_COUNT,
                "UNSOLICITED_REPORT_INTERVAL": igmp_globals.UNSOLICITED_REPORT_INTERVAL,
                "VERSION_1_ROUTER_PRESENT_TIMEOUT": igmp_globals.VERSION_1_ROUTER_PRESENT_TIMEOUT,
            },
            "Interfaces": {},
        },
        'MLD': {
            "Settings": {
                "ROBUSTNESS_VARIABLE": mld_globals.ROBUSTNESS_VARIABLE,
                "QUERY_INTERVAL": mld_globals.QUERY_INTERVAL,
                "QUERY_RESPONSE_INTERVAL": mld_globals.QUERY_RESPONSE_INTERVAL,
                "MULTICAST_LISTENER_INTERVAL": mld_globals.MULTICAST_LISTENER_INTERVAL,
                "OTHER_QUERIER_PRESENT_INTERVAL": mld_globals.OTHER_QUERIER_PRESENT_INTERVAL,
                "STARTUP_QUERY_INTERVAL": mld_globals.STARTUP_QUERY_INTERVAL,
                "STARTUP_QUERY_COUNT": mld_globals.STARTUP_QUERY_COUNT,
                "LAST_LISTENER_QUERY_INTERVAL": mld_globals.LAST_LISTENER_QUERY_INTERVAL,
                "LAST_LISTENER_QUERY_COUNT": mld_globals.LAST_LISTENER_QUERY_COUNT,
                "UNSOLICITED_REPORT_INTERVAL": mld_globals.UNSOLICITED_REPORT_INTERVAL,
            },
            "Interfaces": {},
        }
    }

    for if_name, if_value in Main.interfaces.items():
        dict_file["HPIM-DM"]["Interfaces"][if_name] = {}
        dict_file["HPIM-DM"]["Interfaces"][if_name]["ipv4"] = {
            "enabled": True,
        }
        if if_value.get_security_key() != b'':
            dict_file["HPIM-DM"]["Interfaces"][if_name]["ipv4"]["security"] = {
                "identifier": if_value.security_id,
                "algorithm": if_value.hash_function.__name__.split("openssl_")[1],
                "key": if_value.security_key.decode("utf-8")
            }

    for if_name, if_value in Main.interfaces_v6.items():
        if if_name not in dict_file["HPIM-DM"]["Interfaces"]:
            dict_file["HPIM-DM"]["Interfaces"][if_name] = {}

        dict_file["HPIM-DM"]["Interfaces"][if_name]["ipv6"] = {
            "enabled": True,
        }
        if if_value.get_security_key() != b'':
            dict_file["HPIM-DM"]["Interfaces"][if_name]["ipv6"]["security"] = {
                "identifier": if_value.security_id,
                "algorithm": if_value.hash_function.__name__.split("openssl_")[1],
                "key": if_value.security_key.decode("utf-8")
            }

    for if_name in Main.igmp_interfaces.keys():
        dict_file["IGMP"]["Interfaces"][if_name] = {
            "enabled": True,
        }

    for if_name in Main.mld_interfaces.keys():
        dict_file["MLD"]["Interfaces"][if_name] = {
            "enabled": True,
        }

    return yaml.dump(dict_file)


def get_vrfs(file_path):
    """
    Get vrf configuration from yaml file.
    This is only used by Run.py to create the correct daemons accordingly (daemons are bound to specific VRFs).
    """
    with open(file_path) as f:
        data = yaml.load(f, Loader=yaml.FullLoader)
        multicast_vrf = data.get("MulticastVRF", 0)
        unicast_vrf = data.get("UnicastVRF", 254)
        return [multicast_vrf, unicast_vrf]
