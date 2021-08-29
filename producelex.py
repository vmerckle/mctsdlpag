import argparse
import time

import subprocess

def readanyvar(f):
    l = []
    with open(f, "r") as ff:
        s = ff.read().split("\n")
        for line in s[:-1]:
            l.append([x for x in line.split(";")])
    return l
def length(a):
    s = 0
    pred = True
    zero = 0
    for i in a:
        if i != "0":
            s+= 1
            pred = False
        elif pred:
            zero += 1
    return s,zero

def convreasnoble(x, dec=2):
    s = x.split(".")
    a,b = s[0], s[1]
    la,zero = length(a)
    lb,zero = length(b)
    if la >= dec:
        b=""
    else:
        dec -= la
        b = b[:dec+zero]
    s = f"{a}&{b}"
    return s
def convtoints(l):
    out = []
    for i in l:
        if i == "TO":
            out.append("\\multicolumn{2}{c}{TO}")
        elif i == "SO":
            out.append("\\multicolumn{2}{c}{SO}")
        else:
            out.append(convreasnoble(i))
    return out
def convertoneline(l):
    name, l = l[0], l[1:]
    therest = " & ".join([a for a in convtoints(l)])
    return f"        {name} & {therest}\\\\\n"

def convertotex(ll):
    firstline = ll[0]
    howmany = str(len(firstline) - 1)
    others = ll[1:]
    mtop = "&".join(["\multicolumn{2}{c}{"+n+"}" for n in firstline[1:]])
    top="        "+firstline[0] + " & " + mtop + "\\\\\n"
    middle= "".join([convertoneline(x) for x in others])
    return """\\begin{table}
    \\caption{Execution time in seconds}
    \\begin{tabular}{l*"""+howmany+"""{r@{.}l}} 
        \\toprule
"""+top+"        \\midrule\n"+middle+"""        \\bottomrule
    \end{tabular}
\end{table}"""


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    #parser.add_argument("n", help="task number", type=int, default=5, nargs='?')
    #parser.add_argument("max_task_size", help="max task size", type=int, default=10, nargs='?')
    parser.add_argument("filename", help="filename", type=str)
    parser.add_argument("-output", help="output filename", type=str)
    args = parser.parse_args()

    ll = readanyvar(args.filename)
    s = (convertotex(ll))
    with open(args.output, "w") as f:
        f.write(s)
