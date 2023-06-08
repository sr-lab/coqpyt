import os
from pylspclient.lsp_structs import ResponseError
from pylspclient.proof_state import ProofState

file_path = os.path.join(os.getcwd(), 'test.v')

try:
    # symbols = lsp_client.documentSymbol(TextDocumentIdentifier(uri))
    # for symbol in symbols:
    #     print(symbol.detail + ": " + symbol.name + " (" + str(symbol.kind) + ")")
    #     print(symbol.range)
    #     print(symbol.selectionRange)
    #     print()
    state = ProofState(file_path)
    state.exec()
    state.exec()
    print(state.get_current_theorem())

    state.exec(2)
    expr = state.current_step['span']['v']['expr']
    print("INTROS")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec()
    expr = state.current_step['span']['v']['expr']
    print("PRINT")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec()
    expr = state.current_step['span']['v']['expr']
    print("PRINT DOT")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec(19)
    expr = state.current_step['span']['v']['expr']
    print("REWRITE HYP")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec(7)
    expr = state.current_step['span']['v']['expr']
    print("REWRITE 2 HYPS")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec(12)
    expr = state.current_step['span']['v']['expr']
    print("REWRITE ARROW")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec(6)
    expr = state.current_step['span']['v']['expr']
    print("REWRITE")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec(61)
    expr = state.current_step['span']['v']['expr']
    print("SEQUENCE")
    [print(i) for i in expr[:-1]]
    [print(i) for i in expr[-1]]
    print()

    state.exec() # Qed
    state.jump_to_proof()
    print(state.current_step['range'])
    expr = state.current_step['span']['v']['expr']
    print("JUMP")
    [print(i) for i in expr]
    print()

    # state.exec(55)
    # print((state.pos.line, state.pos.character))
    # state.exec()
    # print((state.pos.line, state.pos.character))
    # state.exec()
    # print((state.pos.line, state.pos.character))

    # state.exec(4)
    # print((state.pos.line, state.pos.character))
    # goals = lsp_client.proof_goals(TextDocumentIdentifier(uri), state.pos)
    # print(goals)
    # [print(step, end='') for step in state.next_steps()]
    # print()

    # print(state.proof_steps(symbols[8])) # Definition
    # print(state.proof_steps(symbols[-1])) # Theorem

    # searches = lsp_client.get_searches(TextDocumentIdentifier(uri))
    # print(searches[0].query)
    # print(searches[0].results)
    state.close()
except ResponseError:
    # documentSymbol is supported from version 8.
    print("Failed to document symbols")
