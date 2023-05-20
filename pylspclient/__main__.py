import os
import subprocess
from pylspclient.lsp_structs import Position, TextDocumentItem, TextDocumentIdentifier, ResponseError
from pylspclient.json_rpc_endpoint import JsonRpcEndpoint
from pylspclient.lsp_client import LspClient
from pylspclient.lsp_endpoint import LspEndpoint
from pylspclient.proof_state import ProofState


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
    
    state = ProofState(text)
    state.exec(31)
    goals = lsp_client.proof_goals(TextDocumentIdentifier(uri), state.pos)
    print(goals)
    print(state.next_steps())

    print((state.pos.line, state.pos.character))
    print(str(goals.goals.goals[0].hyps[0].names) + ": " + str(goals.goals.goals[0].hyps[0].ty))
    print(goals.goals.goals[0].ty)
except ResponseError:
    # documentSymbol is supported from version 8.
    print("Failed to document symbols")

# Shutdown
lsp_client.shutdown()
lsp_client.exit()
