import inputCreatorNemo
import os
import time
import random
import json
import subprocess
import networkx
import math

ruleFile = "tc.rls"
folder = "/home/johannes/CertifyingDatalog/Examples/diplomarbeit"
certifyingDatalogPath = "/home/johannes/CertifyingDatalog/.lake/build/bin/certifyingDatalog"
outputformat = "-g"
tries = 1
atomsPerTry = 50

def generateGraph(numNodes, density):
    graph = networkx.gnm_random_graph(numNodes, math.ceil(density*numNodes*(numNodes-1)), directed=True)

    with open("sources/edge.csv", "w") as file:
        for e in graph.edges:
            file.write(str(e[0])+","+str(e[1])+"\n")

def completenessExperiments():
    densities = [0.01, 0.05, 0.1, 0.3]
    numNodes = 100
    tries = 5
    logFile = "log_graph_completeness.txt"
    for density in densities:
        for i in range(0,tries):
            generateGraph(numNodes, density)

            start = time.time()
            subprocess.run(["nmo", "-so" ,ruleFile])
            nemoTime = time.time() - start


            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-t")
            
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".tree.json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run([certifyingDatalogPath, "-c", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            
            with open(logFile , "a") as log:
                log.write(json.dumps({"Type": "tree", "density": density, "numNodes": numNodes, "completeness": True,"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)})+ "\n")

            start = time.time()
            result = subprocess.run([certifyingDatalogPath, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            
            with open(logFile , "a") as log:
                log.write(json.dumps({"Type": "tree", "density": density, "numNodes": numNodes, "completeness": False,"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)})+ "\n")

def graphExperiments():
    densities = [0.01, 0.05, 0.1, 0.3]
    #densities = [0.5]
    numNodes = 100
    tries = 1
    logFile = "log_graphArray.txt"
    for density in densities:
        for i in range(0,tries):
            print(density)
            print(i)
            generateGraph(numNodes, density)

            # Generate datalog result
            start = time.time()
            subprocess.run(["nmo", "-so" ,ruleFile])
            nemoTime = time.time() - start

            # Check only soundness trees
            # print("Start")
            # start = time.time()
            # inputCreatorNemo.main(folder, ruleFile, "-t")
            
            
            # preparation = time.time() - start
            
            # problemFile = ruleFile.split(".")[0] + ".tree.json"

            # with open(problemFile) as file:
            #     problem = json.load(file)
            

            # start = time.time()
            # result = subprocess.run([certifyingDatalogPath, "-c", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            # duration = time.time() - start
            
            # with open(logFile , "a") as log:
            #     log.write(json.dumps({"Type": "tree", "density": density, "numNodes": numNodes, "completeness": True,"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)})+ "\n")

            # start = time.time()
            # result = subprocess.run([certifyingDatalogPath, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            # duration = time.time() - start
            
            # with open(logFile , "a") as log:
            #     log.write(json.dumps({"Type": "tree", "density": density, "numNodes": numNodes, "completeness": False,"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)})+ "\n")
            
            #Check only soundness graph
            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-g")
            
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".graph.json"

            
                

            start = time.time()
            result = subprocess.run([certifyingDatalogPath, "-c", "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start 
            with open(problemFile) as file:
                problem = json.load(file)
                with open(logFile , "a") as log:
                    log.write(json.dumps({"Type": "graph", "density": density, "numNodes": numNodes, "completeness": True, "graph": problem["graph"], "Result": result.stdout, "Nemo time": nemoTime, "Preparation time": str(preparation), "Validation time": str(duration)})+"\n")

            start = time.time()
            result = subprocess.run([certifyingDatalogPath, "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start 
            with open(problemFile) as file:
                problem = json.load(file)
                with open(logFile , "a") as log:
                    log.write(json.dumps({"Type": "graph", "density": density, "numNodes": numNodes, "completeness": False, "graph": problem["graph"], "Result": result.stdout, "Nemo time": nemoTime, "Preparation time": str(preparation), "Validation time": str(duration)})+"\n")


def graphExperiments2():
    densities = [0.5]
    #densities = [0.01, 0.05, 0.1, 0.3]
    numNodes = 100
    tries = 5
    logFile = "log_graph2.txt"
    ruleFiles = ["tc.rls", "tc2.rls"]
    for density in densities:
        for i in range(0,tries):
            for ruleFile in ruleFiles:
                print(density)
                print(i)
                generateGraph(numNodes, density)

                start = time.time()
                subprocess.run(["nmo", "-so" ,ruleFile])
                nemoTime = time.time() - start


                print("Start")
                start = time.time()
                inputCreatorNemo.main(folder, ruleFile, "-t")
                
                
                preparation = time.time() - start
                
                problemFile = ruleFile.split(".")[0] + ".tree.json"

                with open(problemFile) as file:
                    problem = json.load(file)
                

                start = time.time()
                result = subprocess.run([certifyingDatalogPath, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

                duration = time.time() - start
                
                with open(logFile , "a") as log:
                    log.write(json.dumps({"Type": "tree", "density": density, "numNodes": numNodes, "Rule file": ruleFile,"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)})+ "\n")

                print("Start")
                start = time.time()
                inputCreatorNemo.main(folder, ruleFile, "-g")
                
                
                preparation = time.time() - start
                
                problemFile = ruleFile.split(".")[0] + ".graph.json"


                start = time.time()
                result = subprocess.run([certifyingDatalogPath, "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

                duration = time.time() - start 
                with open(problemFile) as file:
                    problem = json.load(file)
                    with open(logFile , "a") as log:
                        log.write(json.dumps({"Type": "graph", "density": density, "numNodes": numNodes, "Rule file": ruleFile, "graph": problem["graph"], "Result": result.stdout, "Nemo time": nemoTime, "Preparation time": str(preparation), "Validation time": str(duration)})+"\n")

def generateChain(length):
    with open("sources/E.csv", "w") as file:
        for i in range(1, length):
            file.write(str(i-1) + "," + str(i) + "\n")

def exponentialExample():
    #sizes = [10]
    sizes = [10,15,20]
    tries = 5   
    ruleFile = "ExponentialTC.rls"

    with open ("ExponentialTCLog.txt", "w") as log:
        pass#Delete previous logs
    
    for size in sizes:
        generateChain(size)
        for i in range(0, tries):
            print("Try:" + str(i) + "Size: " + str(size) +  "\n")
            start = time.time()
            subprocess.run(["nmo", "-so" ,ruleFile])
            nemoTime = time.time() -start

            problemFileGraph = ruleFile.split(".")[0] + ".graph.json"

            print("graph")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-g", f"T(0,{size-1})")
            preparationTime = time.time() -start
            start = time.time()

            graphResult = subprocess.run([certifyingDatalogPath, "-g", problemFileGraph], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            endGraph = time.time() - start

            with open(problemFileGraph) as file:
                problem = json.load(file)
            with open ("ExponentialTCLog.txt", "a") as log:
                log.write(json.dumps({"type": "graph", "problem":problem["graph"],"Result": graphResult.stdout, "Nemo time": str(nemoTime), "Validation time": str(endGraph), "Preparation time": preparationTime, "size": size})+"\n")

            problemFileTree = ruleFile.split(".")[0] + ".tree.json"

            print("tree")

            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-t", f"T(0,{size-1})")
            preparationTime = time.time() -start
            start = time.time()

            treeResult = subprocess.run([certifyingDatalogPath,  problemFileTree], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            endTree = time.time() - start

            with open(problemFileTree) as file:
                problem = json.load(file)

            with open ("ExponentialTCLog.txt", "a") as log:

                log.write(json.dumps({"type": "tree", "problem":problem["trees"],"Result": treeResult.stdout, "Nemo time": str(nemoTime),"Preparation time": preparationTime, "Validation time": str(endTree), "size": size})+"\n")

def galenExperiments():
    atomNumbers = [1,10,100,1000,10000]
    tries = 5
    ruleFile = "el-calc.rls"
    with open("log_galen.txt" , "w") as log:
        for atomNumber in atomNumbers:
            for i in range(0,tries):

                start = time.time()
                subprocess.run(["nmo", "-so" ,ruleFile])
                nemoTime = time.time() - start

                model = inputCreatorNemo.getModel()
                atoms = []
                while len(atoms) < atomNumber:
                    atom = random.choice(model)
                    if atom not in atoms:
                        atoms.append(atom)

                print("Start")
                start = time.time()
                inputCreatorNemo.main(folder, ruleFile, "-t", *atoms)
                
                preparation = time.time() - start
                
                problemFile = ruleFile.split(".")[0] + ".tree.json"

                with open(problemFile) as file:
                    problem = json.load(file)
                

                start = time.time()
                
                result = subprocess.run([certifyingDatalogPath, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

                duration = time.time() - start
                
                log.write(json.dumps({"trees": problem["trees"], "Result": result.stdout, "Nemo time": nemoTime, "Preparation time": str(preparation), "Validation time": str(duration), "numberAtoms": atomNumber})+ "\n")

                print("Start")
                start = time.time()
                inputCreatorNemo.main(folder, ruleFile, "-g", *atoms)
                
                preparation = time.time() - start
                
                problemFile = ruleFile.split(".")[0] + ".graph.json"

                with open(problemFile) as file:
                    problem = json.load(file)
                

                start = time.time()
                result = subprocess.run([certifyingDatalogPath, "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)


                duration = time.time() - start 
                
                log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Nemo time": nemoTime, "Preparation time": str(preparation), "Validation time": str(duration), "numberAtoms": atomNumber})+"\n")

def ographExperiments():
    #densities = [0.01, 0.05, 0.1, 0.3]
    densities = [0.5]
    numNodes = 100
    ruleFile = "tc.rls"
    tries = 1
    for density in densities:
        for i in range(0,tries):
            print(density)
            generateGraph(numNodes, density)

            # Generate datalog result
            subprocess.run(["nmo", "-so" ,ruleFile])

            inputCreatorNemo.main(folder, ruleFile, "-o")
            problemFile = ruleFile.split(".")[0] + ".ograph.json"
            with open(problemFile) as file:
                object= json.load(file)
                print("p")

            start = time.time()
            result = subprocess.run([certifyingDatalogPath, "-o", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            print(duration) 



ographExperiments()
#graphExperiments2()
#galenExperiments()
#exponentialExample()
