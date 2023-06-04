import os
import subprocess
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier, ResponseError
from pylspclient.json_rpc_endpoint import JsonRpcEndpoint
from pylspclient.coq_lsp_client import CoqLspClient
from pylspclient.lsp_endpoint import LspEndpoint
from pylspclient.proof_state import ProofState


root_path = os.getcwd()
root_uri = 'file://' + root_path

# Initialize client
proc = subprocess.Popen('coq-lsp', stdout=subprocess.PIPE, stdin=subprocess.PIPE)
json_rpc_endpoint = JsonRpcEndpoint(proc.stdin, proc.stdout)
lsp_endpoint = LspEndpoint(json_rpc_endpoint)
lsp_client = CoqLspClient(lsp_endpoint)
workspaces = [{'name': 'coq-lsp', 'uri': root_uri}]
lsp_client.initialize(proc.pid, '', root_uri, { "show_coq_info_messages": True, "eager_diagnostics": False }, {}, 'off', workspaces)
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
    state.exec(55)
    print((state.pos.line, state.pos.character))
    state.exec()
    print((state.pos.line, state.pos.character))
    state.exec()
    print((state.pos.line, state.pos.character))

    state.exec(4)
    print((state.pos.line, state.pos.character))
    goals = lsp_client.proof_goals(TextDocumentIdentifier(uri), state.pos)
    print(goals)
    [print(step, end='') for step in state.next_steps()]
    print()

    print(state.proof_steps(symbols[8])) # Definition
    print(state.proof_steps(symbols[-1])) # Theorem

    searches = lsp_client.get_searches(TextDocumentIdentifier(uri))
    print(searches[0].query)
    print(searches[0].results)

    print(lsp_client.get_document(TextDocumentIdentifier(uri)))
except ResponseError:
    # documentSymbol is supported from version 8.
    print("Failed to document symbols")

# Shutdown
lsp_client.shutdown()
lsp_client.exit()
