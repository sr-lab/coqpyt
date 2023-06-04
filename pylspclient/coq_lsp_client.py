import time
from pylspclient.lsp_client import LspClient
from pylspclient import lsp_structs
from pylspclient import coq_lsp_structs

class CoqLspClient(LspClient):
    def __init__(self, lsp_endpoint):
        super().__init__(lsp_endpoint)

    def didOpen(self, textDocument: lsp_structs.TextDocumentItem):
        super().didOpen(textDocument)
        while self.lsp_endpoint.completed_operation != True:
            time.sleep(1)

    def proof_goals(self, textDocument, position):
        def parse_goal(goal):
            for hyp in goal["hyps"]:
                 if "def" in hyp:
                    hyp["definition"] = hyp["def"]
                    hyp.pop("def")
            hyps = [coq_lsp_structs.Hyp(**hyp) for hyp in goal["hyps"]]
            ty = None if "ty" not in goal else goal["ty"]
            return coq_lsp_structs.Goal(hyps, ty)
        
        def parse_goals(goals):
            return [parse_goal(goal) for goal in goals]

        result_dict = self.lsp_endpoint.call_method("proof/goals", textDocument=textDocument, position=position)
        result_dict["textDocument"] = lsp_structs.VersionedTextDocumentIdentifier(**result_dict["textDocument"])
        result_dict["position"] = lsp_structs.Position(result_dict["position"]["line"], result_dict["position"]["character"])

        if result_dict["goals"] is not None:
            goal_config = result_dict["goals"]
            goals = parse_goals(goal_config["goals"])
            stack = [(parse_goals(t[0]), parse_goals(t[1])) for t in goal_config["stack"]]
            bullet = None if "bullet" not in goal_config else goal_config["bullet"]
            shelf = parse_goals(goal_config["shelf"])
            given_up = parse_goals(goal_config["given_up"])
            result_dict["goals"] = coq_lsp_structs.GoalConfig(goals, stack, shelf, given_up, bullet=bullet)
        
        for i, message in enumerate(result_dict["messages"]):
             if not isinstance(message, str):
                  if message["range"]:
                       message["range"] = lsp_structs.Range(**message["range"])
                  result_dict["messages"][i] = coq_lsp_structs.Message(**message)

        return coq_lsp_structs.GoalAnswer(**result_dict)
    
    def get_queries(self, textDocument, keyword):
        '''
        keyword might be Search, Print, Check, etc...
        '''
        uri = textDocument.uri
        if textDocument.uri.startswith('file://'):
             uri = uri[7:]

        with open(uri, 'r') as doc:
            if textDocument.uri not in self.lsp_endpoint.diagnostics:
                return []
            lines = doc.readlines()
            diagnostics = self.lsp_endpoint.diagnostics[textDocument.uri]
            searches = {}

            for diagnostic in diagnostics:
                command = lines[diagnostic.range["start"]["line"]:diagnostic.range["end"]["line"] + 1]
                if len(command) == 1:
                    command[0] = command[0][diagnostic.range["start"]["character"]:diagnostic.range["end"]["character"] + 1]
                else:
                    command[0] = command[0][diagnostic.range["start"]["character"]:]
                    command[-1] = command[-1][:diagnostic.range["end"]["character"] + 1]
                command = ''.join(command).strip()

                if command.startswith(keyword):
                    query = command[len(keyword) + 1:-1]
                    if query not in searches:
                         searches[query] = []
                    searches[query].append(diagnostic.message)

            res = []
            for query, results in searches.items():
                res.append(coq_lsp_structs.Query(query, results))

        return res
    
    def get_document(self, textDocument):
        result_dict = self.lsp_endpoint.call_method("coq/getDocument", textDocument=textDocument)
        return result_dict