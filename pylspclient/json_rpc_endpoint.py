from __future__ import print_function
import json
import logging
from pylspclient import lsp_structs
import threading

JSON_RPC_REQ_FORMAT = "Content-Length: {json_string_len}\r\n\r\n{json_string}"
LEN_HEADER = "Content-Length: "
TYPE_HEADER = "Content-Type: "


# TODO: add content-type


class MyEncoder(json.JSONEncoder): 
    """
    Encodes an object in JSON
    """
    def default(self, o): # pylint: disable=E0202
        return o.__dict__ 


class JsonRpcEndpoint(object):
    '''
    Thread safe JSON RPC endpoint implementation. Responsible to receive and send JSON RPC messages, as described in the
    protocol. More information can be found: https://www.jsonrpc.org/
    '''
    def __init__(self, stdin, stdout):
        self.stdin = stdin
        self.stdout = stdout
        self.read_lock = threading.Lock() 
        self.write_lock = threading.Lock()
        self.message_size = None

    @staticmethod
    def __add_header(json_string):
        '''
        Adds a header for the given json string
        
        :param str json_string: The string
        :return: the string with the header
        '''
        return JSON_RPC_REQ_FORMAT.format(json_string_len=len(json_string), json_string=json_string)


    def send_request(self, message):
        '''
        Sends the given message.

        :param dict message: The message to send.            
        '''
        try:
            json_string = json.dumps(message, cls=MyEncoder)
            jsonrpc_req = self.__add_header(json_string)
            with self.write_lock:
                self.stdin.write(jsonrpc_req.encode())
                self.stdin.flush()
        except BrokenPipeError as e:
            logging.error(e)


    def recv_response(self):
        '''        
        Receives a message.

        :return: a message
        '''
        with self.read_lock:
            if self.message_size:
                if self.message_size.isdigit():
                    self.message_size = int(self.message_size)
                else:
                    raise lsp_structs.ResponseError(lsp_structs.ErrorCodes.ParseError, "Bad header: size is not int")
            while True:
                #read header
                line = self.stdout.readline()
                if not line:
                    # server quit
                    return None
                line = line.decode("utf-8")
                if not line.endswith("\r\n"):
                    raise lsp_structs.ResponseError(lsp_structs.ErrorCodes.ParseError, "Bad header: missing newline")
                #remove the "\r\n"
                line = line[:-2]
                if line == "":
                    # done with the headers
                    break
                elif line.startswith(LEN_HEADER):
                    line = line[len(LEN_HEADER):]
                    if not line.isdigit():
                        raise lsp_structs.ResponseError(lsp_structs.ErrorCodes.ParseError, "Bad header: size is not int")
                    self.message_size = int(line)
                elif line.startswith(TYPE_HEADER):
                    # nothing todo with type for now.
                    pass
                else:
                    line = line.split(LEN_HEADER)
                    if len(line) == 2: self.message_size = line[1]
                    raise lsp_structs.ResponseError(lsp_structs.ErrorCodes.ParseError, "Bad header: unknown header")
            if not self.message_size:
                raise lsp_structs.ResponseError(lsp_structs.ErrorCodes.ParseError, "Bad header: missing size")

            jsonrpc_res = self.stdout.read(self.message_size).decode("utf-8")
            self.message_size = None
            return json.loads(jsonrpc_res)
