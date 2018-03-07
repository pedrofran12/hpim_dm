import ipaddress

class Metric(object):
    def __init__(self, metric_preference: int = 0x7FFFFFFF, route_metric: int = 0xFFFFFFFF):
        self._metric_preference = metric_preference
        self._route_metric = route_metric

    def is_better_than(self, other):
        if self.metric_preference != other.metric_preference:
            return self.metric_preference < other.metric_preference
        else:
            return self.route_metric < other.route_metric

    def __eq__(self, other):
        return self.metric_preference == other.metric_preference and self.route_metric == other.route_metric

    @property
    def metric_preference(self):
        return self._metric_preference

    @metric_preference.setter
    def metric_preference(self, value):
        self._metric_preference = value

    @property
    def route_metric(self):
        return self._route_metric

    @route_metric.setter
    def route_metric(self, value):
        self._route_metric = value


class AssertMetric(Metric):
    def __init__(self, metric_preference: int = 0x7FFFFFFF, route_metric: int = 0xFFFFFFFF, ip_address: str = "0.0.0.0"):
        super().__init__(metric_preference, route_metric)

        if type(ip_address) is str:
            ip_address = ipaddress.ip_address(ip_address)

        self._ip_address = ip_address

    def is_better_than(self, other):
        return super().is_better_than(other) or (super().__eq__(other) and self.ip_address > other.ip_address)
        #is_better = super().is_better_than(other) or (super().__eq__(other) and self.ip_address > other.ip_address)
        #print("MP1:", self.metric_preference, "M1:", self.route_metric, "IP1", self.get_ip(), "MP2:", other.metric_preference, "M2", other.route_metric, "IP2", other.get_ip(), "RESULT:", is_better)
        #return is_better

    '''
        if self.metric_preference != other.metric_preference:
            return self.metric_preference < other.metric_preference
        elif self.route_metric != other.route_metric:
            return self.route_metric < other.route_metric
        else:
            return self.ip_address > other.ip_address
    '''

    '''
    def __eq__(self, other):
        return super().__eq__(other) and self.ip_address == other.ip_address
    '''

    def is_worse(self, other):
        return not self.is_better_than(other)

    @staticmethod
    def infinite_assert_metric():
        '''
        @type metric: AssertMetric
        '''
        return AssertMetric()

    @staticmethod
    def spt_assert_metric(tree_if):
        '''
        @type metric: AssertMetric
        @type tree_if: TreeInterface
        '''
        (source_ip, _) = tree_if.get_tree_id()
        import UnicastRouting
        (metric_preference, metric_cost, _) = UnicastRouting.get_metric(source_ip)
        return AssertMetric(metric_preference, metric_cost, tree_if.get_ip())


    def i_am_assert_winner(self, tree_if):
        return self.get_ip() == tree_if.get_ip()

    @property
    def ip_address(self):
        return self._ip_address

    @ip_address.setter
    def ip_address(self, value):
        if type(value) is str:
            value = ipaddress.ip_address(value)

        self._ip_address = value

    def get_ip(self):
        return str(self._ip_address)
