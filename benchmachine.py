import argparse
import time
import os

import subprocess
from multiprocessing import Pool, TimeoutError
from producelex import convertotex

def run(cmd, timeout=None):
    reachedTimeout = False
    start_time = time.time()
    try:
        x = subprocess.check_output(cmd.split(" "), timeout=timeout)
    except subprocess.TimeoutExpired as e:
        reachedTimeout = True
        x = e.output
    except Exception as e:
        return -1, None
    elapsed_time = time.time() - start_time
    if reachedTimeout:
        return timeout, None
    if x is None:
        return elapsed_time, None
    y = x.decode("utf-8")
    lines = y.split("\n")
    z = lines[-1].strip().split(",")
    return elapsed_time, bool(z[0])
def runx(cmd, timeout=None):
    reachedTimeout = False
    start_time = time.time()
    try:
        x = subprocess.check_output(cmd.split(" "), timeout=timeout)
    except subprocess.TimeoutExpired as e:
        reachedTimeout = True
        x = e.output
    except Exception as e:
        print("SO!    ",cmd)
        return -1000
    elapsed_time = time.time() - start_time
    if reachedTimeout:
        print("TO!TO=",timeout, "   ", cmd)
        return -1000
    if x is None:
        print("Other problem!    ",cmd)
        return -1000
    y = x.decode("utf-8")
    lines = y.split("\n")
    z = lines[-1].strip().split(",")
    print(z, "ran", cmd, " in ", elapsed_time)
    return elapsed_time

# print 2darray (list of list) to .csv
def writeanyvar(l, fname, delete=True):
    ss = []
    for vx in l:
        ss.append(";".join([str(i) for i in vx]))
    s = "\n".join(ss) + "\n"

    filemod = "w"
    if not delete:
        filemod = "a"

    with open(fname, filemod) as f:
        f.write(s)


def readanyvar(f):
    l = []
    with open(f, "r") as ff:
        s = ff.read().split("\n")
        for line in s[:-1]:
            l.append([x for x in line.split(";")])
    return l

def run_bench(cmd, timeout, n_sample, encoding):
    total_time = 0
    cmd = cmd+" "+encoding
    for i in range(n_sample):
        elapsed_time, x = run(cmd, timeout)
        #elapsed_time, x = 1.2 + len(cmd), True
        print(f"ran {cmd} {i}th time")
        if elapsed_time == -1:
            print("stack overflow")
            return "SO"
        if x is None:
            if total_time != 0:
                print("timeout")
                return timeout
            return "TO"
        else:
            total_time += elapsed_time
        print(f"took {elapsed_time}")
    return total_time/n_sample

def run_bench_multi(pool, cmd, timeout, n_sample, encoding):
    cmd = cmd+" "+encoding
    res = [pool.apply_async(runx, (cmd, timeout)) for i in range(n_sample)]
    #print([r.get(timeout=timeout+1) for r in res])
    return res


def many_parameters_one_encoding(cmds, timeout, n_sample, encoding):
    res = []
    for cmd,cmdname in cmds:
        res.append(run_bench(cmd, timeout, n_sample, encoding))
    return res

def many_parameters_one_encoding_multi(pool, cmds, timeout, n_sample, encoding):

    res = []
    for cmd,cmdname in cmds:
        res.append(run_bench_multi(pool, cmd, timeout, n_sample, encoding))
    return res

def many_parameters_one_encoding_constant_multi(cores, cmds, timeout, n_sample, encoding):
    with Pool(processes=cores) as pool:
        firstline = ["C constant"]
        for cmd,cmdname in cmds:
            firstline.append(cmdname)
        alllines = [firstline]
        encoding,encodingname = encoding
        res = []
        for c in [0.0001, 0.001, 0.01,0.03,0.07,0.09, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1, 1.1, 1.2, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9, 2, 4, 8, 1024]:
            resres = []
            for cmd, cmdname in cmds:
                resres.append(run_bench_multi(pool, f"{cmd} -c {c}", timeout, n_sample, encoding))
            res.append((resres,f"{c}"))
        
        for line,encodingname in res:
            colres = []
            for col in line:
                s = 0
                timeouted = False
                souted = False
                for sampl in col:
                    si = (sampl.get(timeout=timeout+1))
                    s += si
                    if si < -100:
                        souted = True
                    elif si < 0:
                        timeouted = True
                s = s/len(col)
                if souted:
                    s = "SO"
                elif timeouted:
                    s = "TO"

                colres.append(s)
            alllines.append([encodingname] + colres)

        for x in alllines:
            print(x)
        return alllines

def many_parameters_one_encoding_ntant_multi(cores, cmds, timeout, n_sample, encoding):
    with Pool(processes=cores) as pool:
        firstline = ["Nb rollout"]
        for cmd,cmdname in cmds:
            firstline.append(cmdname)
        alllines = [firstline]
        encoding,encodingname = encoding
        res = []
        for c in [1,2,10,20,100]:
            resres = []
            for cmd, cmdname in cmds:
                resres.append(run_bench_multi(pool, f"{cmd} --nplayout {c}", timeout, n_sample, encoding))
            res.append((resres,f"{c}"))
        
        for line,encodingname in res:
            colres = []
            for col in line:
                s = 0
                for sampl in col:
                    s += (sampl.get(timeout=timeout+1))
                s = s/len(col)
                if s < -100:
                    s = "SO"
                elif s < 0:
                    s = "TO"

                colres.append(s)
            alllines.append([encodingname] + colres)

        for x in alllines:
            print(x)
        return alllines



def many_parameters_one_encoding_constant(cmds, timeout, n_sample, encoding):
    firstline = ["C constant"]
    for cmd,cmdname in cmds:
        firstline.append(cmdname)
    alllines = [firstline]

    encoding,encodingname = encoding
    for c in [0.0001, 0.001, 0.01,0.03,0.07,0.09, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1, 1.1, 1.2, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9, 2, 4, 8, 1024]:
        res = [f"{c}"]
        for cmd,cmdname in cmds:
            res.append(run_bench(f"{cmd} -c {c}", timeout, n_sample, encoding))
        alllines.append(res)
    return alllines

#return 2d array, x = parameters --->, y = encodings
def many_parameters_many_encodings(cmds, timeout, n_sample, encodings):
    firstline = ["Problem"]
    for cmd,cmdname in cmds:
        firstline.append(cmdname)
    alllines = [firstline]
    for encoding,encodingname in encodings:
        res = many_parameters_one_encoding(cmds, timeout, n_sample, encoding)
        alllines.append([encodingname] + res)
    return alllines
 
#return 2d array, x = parameters --->, y = encodings
def many_parameters_many_encodings_multi(cores, cmds, timeout, n_sample, encodings):
    with Pool(processes=cores) as pool:
        firstline = ["Problem"]
        for cmd,cmdname in cmds:
            firstline.append(cmdname)
        alllines = [firstline]
        res = []
        for encoding,encodingname in encodings:
            res.append((many_parameters_one_encoding_multi(pool, cmds, timeout, n_sample, encoding), encodingname))
        
        for line,encodingname in res:
            colres = []
            for col in line:
                s = 0
                for sampl in col:
                    s += (sampl.get(timeout=timeout+1))
                s = s/len(col)
                if s < -100:
                    s = "SO"
                elif s < 0:
                    s = "TO"

                colres.append(s)
            alllines.append([encodingname] + colres)

        for x in alllines:
            print(x)
        return alllines

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    #parser.add_argument("n", help="task number", type=int, default=5, nargs='?')
    #parser.add_argument("max_task_size", help="max task size", type=int, default=10, nargs='?')
    parser.add_argument("filename", help="test", type=str)
    parser.add_argument("-output", help="test", type=str)
    parser.add_argument("-core", help="number of cores", default=1, type=int)
    parser.add_argument("-test", help="test", type=str, default="manymany", nargs='?')
    parser.add_argument("-timeout", help="timeout in s", type=int, default=1, nargs='?')
    parser.add_argument("-samples", help="number of samples", type=int, default=1, nargs='?')
    parser.add_argument("-algos", help="algo to select, ex:1,2,3", type=str)
    parser.add_argument("-encodings", help="encoding to select, ex:1,2,3", type=str)
    args = parser.parse_args()
    allallalgo = [
            ("MCTS", "MCTS"),
            ("MCTS --quicksolver propositional", "MCTS 1"),
            ("MCDS", "MCDS"),
            ("MCDS --quicksolver propositional", "MCDS 1"),
            ("MCDS --quicksolver allbutkleene", "MCDS 2"),
            ("MCDS --quicksolver deterministic", "MCDS 3"),
            ("MCDS --quicksolver smallsize", "MCDS 4"),
            ("MCDSn --nplayout 1", "MCDSn"),
            ("MCDSn --quicksolver propositional --nplayout 1", "MCDSn 1"),
            ("MCDSn --quicksolver propositional --nplayout 2", "MCDSn2 1"),
            ("MCDSn --quicksolver propositional --nplayout 4", "MCDSn4 1"),
            ("MCDSn --quicksolver propositional --nplayout 10", "MCDSn10 1"),
            ("MCDSn --quicksolver propositional --nplayout 20", "MCDSn20 1"),
            ("MCDSn --quicksolver propositional --nplayout 100", "MCDSn100 1"),
            ("simple", "Simple"),
            ("naive", "Naive")
            ]
    if args.algos is None:
        print("Algo to select : with -algos 1,4,5...")
        for i, algo in enumerate(allallalgo):
            print(i+1, algo)
        exit(0)
    algoint = args.algos.split(",")
    algoint = [int(x) for x in algoint]
    allalgo = []
    for i,algo in enumerate(allallalgo):
        if (i+1) in algoint:
            allalgo.append(algo)
    allencodings = [
            ("simpletrap.pa", "Simple trap"),
            ]

    for i in range(1,17):
        allencodings.append((f"hanoi3{i}.pa", f"Hanoi(3,{i})"))
    for i in [180, 500, 1000, 10000]:
        allencodings.append((f"counter{i}.pa", f"Counter({i})"))
    if args.encodings is None:
        print("Encodings to select : with -encodings 1,4,5...")
        for i, encoding in enumerate(allencodings):
            print(i+1, encoding)
        exit(0)
    encodingint = args.encodings.split(",")
    encodingint = [int(x) for x in encodingint]
    encodings = []
    for i,encoding in enumerate(allencodings):
        if (i+1) in encodingint:
            encodings.append(encoding)

    encodings = [(f"encodings/{enc}",encname) for enc,encname in encodings]
    constant = 0.1
    if args.test == "manymany":
        cmds = [(f"mctsdlpag --batch -c {constant} --solver {algo}",algoname) for algo,algoname in allalgo]
        x = many_parameters_many_encodings_multi(args.core, cmds, args.timeout, args.samples, encodings)
    elif args.test == "ctest":
        if len(encodings) > 1 :
            print("Constant optimization : should only include one encoding")
            exit(0)
        cmds = [(f"mctsdlpag --batch --solver {algo}",algoname) for algo,algoname in allalgo]
        x = many_parameters_one_encoding_constant_multi(args.core, cmds, args.timeout, args.samples, encodings[0])

    elif args.test == "ntest":
        if len(encodings) > 1 :
            print("Constant optimization : should only include one encoding")
            exit(0)
        cmds = [(f"mctsdlpag --batch -c {constant} --solver {algo}",algoname) for algo,algoname in allalgo]
        x = many_parameters_one_encoding_ntant_multi(args.core, cmds, args.timeout, args.samples, encodings[0])
    writeanyvar(x, "tables/"+args.filename+".data")
    xs = readanyvar("tables/"+args.filename+".data")
    s = convertotex(xs, args.timeout, args.samples, args.filename)
    with open("tables/"+args.filename+".tex", "w") as f:
        f.write(s)
