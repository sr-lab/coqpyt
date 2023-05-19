import os
import subprocess
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier, ResponseError
from pylspclient.json_rpc_endpoint import JsonRpcEndpoint
from pylspclient.lsp_client import LspClient
from pylspclient.lsp_endpoint import LspEndpoint


root_path = os.getcwd()
root_uri = 'file://' + root_path

# Initialize client
proc = subprocess.Popen('coq-lsp', stdout=subprocess.PIPE, stdin=subprocess.PIPE)
json_rpc_endpoint = JsonRpcEndpoint(proc.stdin, proc.stdout)
lsp_endpoint = LspEndpoint(json_rpc_endpoint)
lsp_client = LspClient(lsp_endpoint)
workspaces = [{'name': 'coq-lsp', 'uri': root_uri}]
lsp_client.initialize(proc.pid, '', root_uri, {}, {}, 'off', workspaces)
lsp_client.initialized()

# Open file
file_path = os.path.join(root_path, 'test.v')
uri = "file://" + file_path
text = open(file_path, "r").read()
languageId = 'coq'
version = 1
lsp_client.didOpen(TextDocumentItem(uri, languageId, version, text))

try:
    symbols = lsp_client.documentSymbol(TextDocumentIdentifier(uri))
    for symbol in symbols:
        print(symbol.detail + ": " + symbol.name + " (" + str(symbol.kind) + ")")
        print(symbol.range)
        print(symbol.selectionRange)
        print()
except ResponseError:
    # documentSymbol is supported from version 8.
    print("Failed to document symbols")

# Shutdown
lsp_client.shutdown()
lsp_client.exit()
