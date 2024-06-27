import sys
import json
import os
import re
from rfc3987 import parse
import subprocess

sys.setrecursionlimit(5000)

nmo = "~/workspace/github/nemo/target/release/nmo"

def normalizeQuotationmarks(s):
    return ''.join(s.replace("\"", "").split())


def getTree(object):
    children = []
    if "premises" in object:
        for atom in object["premises"]:
            label = normalizeQuotationmarks(atom)
            children.append({"node": {"label": label, "children": []}})
    label = normalizeQuotationmarks(object["conclusion"])

    tree = {"node": {"label": label, "children": children}}
    return tree

def expandTree(tree1, tree2):
    currNode = tree1["node"]

    if currNode["label"] == tree2["node"]["label"]:
        return tree2
    
    newChildren = []

    for child in currNode["children"]:
        newChildren.append(expandTree(child, tree2))

    return {"node": {"label": currNode["label"],"children":  newChildren}}



def parseTrees(json_object):
    trees = []
    for atom in json_object["finalConclusion"]:
        trees.append({"node": {"label": normalizeQuotationmarks(atom), "children": []}})

    leafs = list(map(lambda t: set([t["node"]["label"]]), trees))

    changed = True

    while changed:
        changed = False
        for j in range(0, len(json_object["inferences"])):
            inference = json_object["inferences"][j]

            for i in range(0, len(trees)):
                if normalizeQuotationmarks(inference["conclusion"]) in leafs[i]:
                    changed = True
                    trees[i] = expandTree(trees[i], getTree(inference))
                    leafs[i].remove(normalizeQuotationmarks(inference["conclusion"]))
                    for inf in inference["premises"]:
                        leafs[i].add(normalizeQuotationmarks(inf))
    return trees

def getModel():
    model = []
    for filename in os.listdir("results"):
        with open("results/" + filename, "r") as f:
            filename = filename.split(".")[0]
            for line in f:
                if line != "":
                    line = line.replace("\n", "")
                    model.append(filename + "(" + line + ")")
    return model

def elementForCommandLine(s):
    result = re.match(r"(.+)\((.+)\)",s)
    newElements = []
    for element in result[2].split(","):
        try: 
            parse(element[1:-1], rule='IRI')
            newElements.append('<' + element[1:-1] + '>')
        except ValueError:
            newElements.append('"' + element + '"')

    return result[1] + "(" + ",".join(newElements) +  ")"

def tokenize(line):
    currToken = ""
    tokens = []

    for symbol in line:
        if symbol == "(" or symbol == ")":
            if currToken == "":
                tokens.append(symbol)
            else:
                tokens.append(currToken)
                currToken = ""
                tokens.append(symbol)
        elif symbol == "," or symbol == " ":
            if currToken == "":
                continue
            tokens.append(currToken)
            currToken = ""
        else:
            currToken = currToken + symbol

    return tokens

def convertNemoAtomToJson(tokens):
    symbol = tokens.pop(0)
    terms = []
    for token in tokens:
        if token == "(" or token == ")":
            continue
        if token.startswith("?"):
            terms.append({"variable": token})
        else:
            terms.append({"constant": token})
    
    return {"symbol": symbol, "terms": terms}

def convertListNemoAtomsToJson(tokens):
    stack = []
    atoms = []
    for token in tokens:
        if token == ")":
            stack.append(")")
            atoms.append(convertNemoAtomToJson(stack))
            stack = []
        else:
            stack.append(token)
    return atoms

def convertNemoProgramToJson(lines):
    lines = filter(lambda x: not x.startswith("%"), lines)


    program = "".join(lines)

    lines = program.split(".\n")

    transformedLines = []
    for line in lines:
        line = "".join(line.split())
        line = normalizeQuotationmarks(line)
        if line.startswith("@"): 
            continue
        ruleSplit = line.split(":-")

        if len(ruleSplit) == 1:
            heads = convertListNemoAtomsToJson(tokenize(line))
            for head in heads:
                transformedLines.append({"head": head, "body": []})
        else:
            heads = convertListNemoAtomsToJson(tokenize(ruleSplit[0]))

            body = convertListNemoAtomsToJson(tokenize(ruleSplit[1]))
            for head in heads:
                transformedLines.append({"head": head, "body": body})
    return transformedLines

def convertNemoTreeAtomsToJson(tree):
    newLabel = convertNemoAtomToJson(tokenize(tree["node"]["label"]))
    
    newChildren = []
    for child in tree["node"]["children"]:
        newChildren.append(convertNemoTreeAtomsToJson(child))
    
    return {"node": {"label": newLabel, "children": newChildren}}

def treeMembers(tree):
    members = set()

    members.add(tree["node"]["label"])

    for child in tree["node"]["children"]:
        members.update(treeMembers(child))
    
    return members

def filterTrees(treeList):
    model = set()
    filteredTrees = []

    for tree in treeList:
        if tree["node"]["label"] in model:
            continue
        else:
            filteredTrees.append(convertNemoTreeAtomsToJson(tree))
            model.update(treeMembers(tree))

    return filteredTrees

def convertProofTreeToJson(tree):
    label = convertNemoAtomToJson(tokenize(normalizeQuotationmarks(tree["node"]["label"])))

    children = map(convertProofTreeToJson, tree["node"]["children"])

    return {"node": {"label": label, "children": list(children)}}

def parseGraph (json_object):
    edges = []

    for conclusion in json_object["finalConclusion"]:
        atom = convertNemoAtomToJson(tokenize(normalizeQuotationmarks(conclusion)))
        edges.append({"vertex": atom, "successors": []})
    
    for inf in json_object["inferences"]:
        end = convertNemoAtomToJson(tokenize(normalizeQuotationmarks(inf["conclusion"])))
        edges.append({"vertex": end, "successors": list(map(lambda x: convertNemoAtomToJson(tokenize(normalizeQuotationmarks(x))), inf["premises"]))})

    return {"edges": edges}

def parseOrderedGraph (json_object):
    edges = []

    for inf in json_object["inferences"]:
        edges.append((inf["conclusion"], inf["premises"]))        

    #toposort
    edgeList = []
    topologicalsort = {}
    currNum = 0
    changed = True

    while changed:
        changed = False
        for edge in edges:
            if edge[0] in topologicalsort.keys():
                continue
            containPredecessors = True
            for predecessor in edge[1]:
                if not predecessor in topologicalsort.keys():
                    containPredecessors = False
                    break
            
            if containPredecessors is True:
                topologicalsort[edge[0]] = currNum
                edgeList.append((edge[0], list(map(lambda x: topologicalsort[x], edge[1]))))
                currNum = currNum + 1
                changed = True
                break

    if len(edges) != len(edgeList):
        print("Graph is not acyclic")
        exit(0)
    
    print("done")

    outputEdges = []

    for edge in edgeList:
        label = convertNemoAtomToJson(tokenize(normalizeQuotationmarks(edge[0])))

        outputEdges.append({"label": label, "predecessors": edge[1]})
    
    return outputEdges



def main(*args):
    complete = False
    args = list(args)
    if len(args) == 0:
        print("Empty input")
        return
    else:
        if args[0] == "--help" or args[0] == "-h":
            print("First input: path to folder where the data and results are stored")
            print("Second input: program file name, stored at the path above")
            print("Third input: -t for trees as output format or -g for graph output or -o for an ordered graph output")
            print("Additional inputs may be ground atoms which should be tested")
            print("If no additional arguments are added, then the program will grab everything from the results folder and ask for trees for them.")
            return
        if len(args) == 3:
            complete = True
            ruleFile = args[1]
            folder = args[0]
            if args[2] == "-t":
                format = "tree"
            elif args[2] == "-g":
                format = "graph"
            elif args[2] == "-o":
                format = "ograph"
            else:
                print ("Unknown option. Neither -g nor -t")
                return
        else: 
            folder = args.pop(0)
            ruleFile = args.pop(0)
            formatOpt = args.pop(0)
            if formatOpt == "-t":
                format = "tree"
            elif formatOpt == "-g":
                format = "graph"
            elif formatOpt == "-o":
                format = "ograph"

            else:
                print ("Unknown option. Neither -g nor -t")
                return
            model = args

    problemName = ruleFile.split(".")[0]
    print(problemName)
    originalDir = os.getcwd()
    os.chdir(folder)

    if complete:
        model = getModel()
    
    with open("traceGoal.txt", "w") as file:
        file.write(";".join(map(elementForCommandLine, model)))

    print("nmo  --trace-input-file traceGoal.txt --trace-output temp " + ruleFile)

    os.system("nmo  --trace-input-file traceGoal.txt --trace-output temp " + ruleFile)

    print("Finished nemo process")

    program = []
    with open(ruleFile, "r") as file:
        program = convertNemoProgramToJson(file.readlines())

    if format == "tree":
        trees = []
        with open("temp") as f:
            trees = (parseTrees(json.load(f)))

        newTrees = []
        for tree in trees:
            newTrees.append(convertProofTreeToJson(tree))

        trees = newTrees

        print("Parsed trees")
        
        #trees = filterTrees(trees)

        print("Filtering done")
    

        os.chdir(originalDir)
        with open(problemName + ".tree.json", "w") as f:
            json.dump({"trees": trees, "program": program}, f, ensure_ascii=False)
    elif format == "graph":
        # graph output
        with open("temp") as f:
            graph = (parseGraph(json.load(f)))
        print("Parsed graph")
        
        os.chdir(originalDir)
        with open(problemName + ".graph.json", "w") as f:
            json.dump({"graph": graph, "program": program}, f, ensure_ascii=False)

    elif format == "ograph":
        with open("temp") as f:
            graph = parseOrderedGraph(json.load(f))

        os.chdir(originalDir)
        with open(problemName + ".ograph.json", "w") as f:
            json.dump({"graph": {"vertices": graph}, "program": program}, f, ensure_ascii=False)

