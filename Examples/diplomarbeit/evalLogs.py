import pandas as pd
import json

def treeDepth(tree):
    if tree["children"] is []:
        return 1
    else:
        currdepth = 0
        for child in tree["children"]:
            depth = treeDepth(child)
            if depth > currdepth:
                currdepth = depth
        return currdepth + 1
    
def treeNumNodes(tree):
    numNodes = 1
    for child in tree["node"]["children"]:
        numNodes = numNodes + treeNumNodes(child)
    return numNodes

def graphNumNodes(graph):
    vertices = set()

    for e in graph["edges"]:
        vertex = json.dumps(e["vertex"])
        if  vertex in vertices:
            pass
        else:
            vertices.add(vertex)
        
        for succ in e["successors"]:
            succ = json.dumps(succ)
            if succ in vertices:
                pass
            else:
                vertices.add(succ)
    return len(vertices)


def evalExponentialExample():
    columns = ["Type", "Size", "Number of nodes", "Nemo time", "Preparation time", "Validation time"]

    df = pd.DataFrame(columns=columns)
    outputs = set()
    rows = []
    with open("ExponentialTCLog.txt", "r") as log:
        for line in log:
            data = json.loads(line)
            if data["type"] == "tree":
                numberNodes = 0
                for tree in data["problem"]:
                    numberNodes = numberNodes + treeNumNodes(tree)
            else:
                numberNodes = graphNumNodes(data["problem"])
            rows.append({"Type": data["type"], "Size": data["size"], "Number of nodes": int(numberNodes), "Nemo time": float(data["Nemo time"]), "Preparation time": float(data["Preparation time"]), "Validation time": float(data["Validation time"])})

            if data["Result"] in outputs:
                pass
            else:
                outputs.add(data["Result"])
            df = pd.DataFrame(rows, index = list(range(0, len(rows))))

            groupedDf = df.groupby(["Type", "Size"]).agg({"Number of nodes": ["mean"] , "Nemo time": ["mean", "std"], "Preparation time": ["mean", "std"], "Validation time": ["mean", "std"]})

            groupedDf = groupedDf.style.format(precision=2)
            print(outputs)
            with open("Output.txt", "w") as output:
                output.write(groupedDf.to_latex())

def evalGraph():
    columns = ["Type", "Density", "Completeness", "Number of nodes", "Preparation time", "Validation time"]

    df = pd.DataFrame(columns=columns)
    outputs = set()
    rows = []
    with open("log_graphArray.txt", "r") as log:
        for line in log:
            data = json.loads(line)
            if data["Type"] == "tree":
                numberNodes = 0
                for tree in data["trees"]:
                    numberNodes = numberNodes + treeNumNodes(tree)
            else:
                numberNodes = graphNumNodes(data["graph"])
            rows.append({"Type": data["Type"], "Density": data["density"], "Completeness": data["completeness"], "Number of nodes": int(numberNodes), "Preparation time": float(data["Preparation time"]), "Validation time": float(data["Validation time"])})

            if data["Result"] in outputs:
                pass
            else:
                outputs.add(data["Result"])
            df = pd.DataFrame(rows, index = list(range(0, len(rows))))
            df.style.format(precision=2)

            groupedDf = df.groupby(["Type", "Completeness", "Density"]).agg({"Number of nodes": ["mean", "std"], "Preparation time": ["mean", "std"], "Validation time": ["mean", "std"]})

            groupedDf = groupedDf.style.format(precision=2)
            print(outputs)
            with open("Output.txt", "w") as output:
                output.write(groupedDf.to_latex())

def evalGalen():
    columns = ["Type", "Number of nodes", "Nemo time", "Preparation time", "Validation time"]

    df = pd.DataFrame(columns=columns)
    outputs = set()
    rows = []
    with open("log_galen.txt", "r") as log:
        for line in log:
            data = json.loads(line)

            if "trees" in data.keys():
                numberNodes = 0
                for tree in data["trees"]:
                    numberNodes = numberNodes + treeNumNodes(tree)
                    rowType = "tree"
            else:
                numberNodes = graphNumNodes(data["graph"])
                rowType="graph"


            rows.append({"Type": rowType, "Number of nodes": int(numberNodes), "Number of atoms": data["numberAtoms"], "Preparation time": float(data["Preparation time"]), "Validation time": float(data["Validation time"])})

            if data["Result"] in outputs:
                pass
            else:
                outputs.add(data["Result"])
            df = pd.DataFrame(rows, index = list(range(0, len(rows))))

            groupedDf = df.groupby(["Type", "Number of atoms"]).agg({"Number of nodes": ["mean", "std"], "Preparation time": ["mean", "std"], "Validation time": ["mean", "std"]})

            groupedDf = groupedDf.style.format(precision=2)
            print(outputs)
            with open("Output.txt", "w") as output:
                output.write(groupedDf.to_latex())


def evalGraph2():
    columns = ["Type", "Density", "Completeness", "Number of nodes", "Preparation time", "Validation time"]

    df = pd.DataFrame(columns=columns)
    outputs = set()
    rows = []
    with open("log_graph2.txt", "r") as log:
        for line in log:
            data = json.loads(line)
            if data["Type"] == "tree":
                numberNodes = 0
                for tree in data["trees"]:
                    numberNodes = numberNodes + treeNumNodes(tree)
            else:
                numberNodes = graphNumNodes(data["graph"])
            if data["Rule file"] == "tc.rls":
                programType = "A"
            else:
                programType = "B"
                

            rows.append({"Type": data["Type"], "Density": data["density"], "Program type": programType, "Number of nodes": int(numberNodes), "Preparation time": float(data["Preparation time"]), "Validation time": float(data["Validation time"])})

            if data["Result"] in outputs:
                pass
            else:
                outputs.add(data["Result"])
            df = pd.DataFrame(rows, index = list(range(0, len(rows))))
            df.style.format(precision=2)

            groupedDf = df.groupby(["Type", "Program type", "Density"]).agg({"Number of nodes": ["mean", "std"], "Preparation time": ["mean", "std"], "Validation time": ["mean", "std"]})

            groupedDf = groupedDf.style.format(precision=2)
            print(outputs)
            with open("Output.txt", "w") as output:
                output.write(groupedDf.to_latex())

evalGraph()
