from datetime import datetime as DT
from datetime import timedelta
import configparser, requests
import random, string
import time
import os
import zipfile
from sys import path as syspath
from os import getcwd as osgetcwd
from functools import reduce

syspath.append(osgetcwd())
import xlsxwriter
import json
import io
import xml.etree.ElementTree as ET

syspath.append(osgetcwd())
from libs.product.BaseClass import TestBase
from libs.product.standard import util
from libs.product.standard import FileOperation
from deepdiff import DeepDiff
import re
from dateutil.relativedelta import relativedelta
import dateutil.parser
from pydash import arrays
import ipaddress
import calendar
from dateutil import parser
from dateutil.parser import parse
from requests.auth import HTTPDigestAuth
import dpath.util
from itertools import combinations
from pytz import timezone



# Global Variable Declaration
IsActualARCollected = IsiDRACARCollected = IsRacResetCfgCompleted = IsARToARComparisonCompleted = IsAttributeToARComparisonCompleted = IsBiosARCollected = IsAttributeToARComparisonForBiosCompleted = False
tempFlag = True
chkCert = serverType = ""
compareiDRACARDict = RowNumberDict = jsonDataiDRACAR = compareBiosARDict = {}
AttrbList = []
# Filter/Select
DicAttr = IntAttr = StrAttr = ListAttr = boolAttr = {}


### Custom Exception Handling.
class MyError(Exception):
    def __init__(self, message, cause):
        super(MyError, self).__init__(message + ', caused by ' + repr(cause))
        self.cause = cause
        print("Exception occurred while executing Request module", "ERROR: %s" % (self.cause))


### RedfishCommonFunction class is inherited from Base Class
class RedfishCommonFunction(TestBase):

    ### Constructor 1. Initializing attributes with its default value and pre-setup for running specific Manager Group as per the Test cases
    def __init__(self, conn_type, IP, USER, PASSWD, raccommobj, scpobj=None, defaultpassword=None, ConfigURI=None,
                 ipv6=False, portNumber=443, FCP=True, LicenseCheck=None, disabledynamicuri=True):

        self.conn_type = conn_type
        self.raccommobj = raccommobj
        self.IP = IP
        self.USER = USER
        self.PASSWD = PASSWD
        self.output = {}
        self.i = 0
        self.StepCounter = 0
        self.scpobj = scpobj
        self.COUNT = 1
        self.FileName = None
        self.parse_loop = 0
        self.key_val = []
        self.SAcollection_foldername = None
        self.autoexpandlist = []
        self.FCP = FCP
        self.LicenseCheck=LicenseCheck
        self.MaintenanceWindowStart_Time = ""
        self.InMaintenanceWindowOnReset_Time = ""
        self.updatedCompList = []
        self.sleeptime=0
        self.lastSoftInstallFunc = None
        self.fqdd_list = {}
        self.disable_dynamicUri = disabledynamicuri

        confdict = util.getConfDict(self.COUNT)
        self.defaultpassword = confdict["iDRACInformation"].get("serverdefaultpassword", "")
        self.servertype = confdict["iDRACInformation"].get("servertype", "")
        self.session = False

        if ConfigURI == None:
            try:
                ip = ipaddress.ip_address(str(self.IP))
            except:
                ip  = ipaddress.ip_address("1.1.1.1")
            if ip.version == 6:
                if portNumber == 443:
                    self.ConfigURI = 'https://[' + self.IP + ']'
                else:
                    self.ConfigURI = 'https://[' + self.IP + ':' + str(portNumber) + ']'
            else:
                if portNumber == 443:
                    self.ConfigURI = 'https://' + self.IP
                else:
                    self.ConfigURI = 'https://' + self.IP + ':' + str(portNumber)
        else:
            self.ConfigURI = ConfigURI + self.IP

        if serverType == "":
            self.readConfig()

        self.chkCert = chkCert
        self.serverType = serverType
        self.LicenseFileList = []
        self.EntitlementIDList = []
        self.Licensefiledict = {}  # which stores the description as key and the list of values with EntitlementID and FIlename
        self.LicenseDesc = []
        self.servergen = ""
        self.counter = 0
        # cmd = self.raccommobj.getNewGetSetCommand(group="iDRAC", subgroup="Info", object="ServerGen", action='get')
        # print("Racadm get Command::::::::::::::::::", cmd)
        # result = self.run_check_cmd(self.IP, self.USER, self.PASSWD, cmd, "", notval=True, conn_type=self.conn_type)
        # self.servergen = result.split("=")[-1].strip()
        # self.genint = int(re.search(r'\d+', self.servergen).group())

        cmd = self.raccommobj.getNewGetSetCommand(group="iDRAC", subgroup="Info", action='get')
        print("Racadm get Command::::::::::::::::::", cmd)
        result = self.run_check_cmd(self.IP, self.USER, self.PASSWD, cmd, "", notval=True, conn_type=self.conn_type)
        for eachkey in result.split("\n"):
            if eachkey.__contains__("#Version"):
                self.Version = eachkey.split("=")[-1].strip()
                self.releaseNum = int(self.Version.split(".")[0])
            if eachkey.__contains__("ServerGen"):
                self.servergen = eachkey.split("=")[-1].strip()
            if eachkey.__contains__("Type"):
                split_op = eachkey.split('=')[-1].strip().split(' ')
                if len(split_op) == 1:
                    self.serverType = 'Unknown'
                else:
                    self.serverType = eachkey.split('=')[-1].strip().split(' ')[1]
        self.genint = int(re.search(r'\d+', self.servergen).group())

        ### Reading the property file for inputs
        self.RedfishPropertiesDict = self.readURIProperties()

        # Added to disable DynamicUri attribute
        attribute_value = "Disabled" if self.disable_dynamicUri else "Enabled"
        if self.software_minimum_idrac_version(required_version="6.00.00.00"):
            self.disable_dynamic_uri(attributevalue=attribute_value)

        if self.FCP == True:
            ManagerAttributes_url = str(self.RedfishPropertiesDict["RedfishProperties"]["URI"]["AllManagerURI"][2])
            StatusCode, Status, JsonSchema, Headers, ExecutionTime = self.SetAttributeValue(URI=ManagerAttributes_url,
                                                                                            Datatype='String',
                                                                                            AttributeName="SecureDefaultPassword.1.ForceChangePassword",
                                                                                            AttributeValue="False")

            print('StatusCode=%s\n Status=%s\n JsonSchema=%s\n Headers=%s\n ExecutionTime=%s\n' % (
                StatusCode, Status, JsonSchema, Headers, ExecutionTime))

            exp_code = [200]
            if StatusCode not in exp_code:
                self.fail('Fail:The PATCH method to Disable FCP failed ')
            time.sleep(5)

