import sys,re,os,io,copy

dic = {}

objectDic = {}

declare = ""

methodDic = {
    'split':['(define-fun split ((x String)(c String)) (Array Int String))',0]
}

def param(args):
    exp = " "
    for i in range(0,len(args)):
        if trans(args[i]):
            exp = exp + trans(args[i]) + " "
    exp+=")"
    return exp

def vardic(var):
    global dic
    if var in dic:
        dic[var] = dic[var]+1
    else:
        dic[var] = 0
    global declare
    declare += "(declare-const "+ var +"_"+str(dic[var])+" String)\n"
    return ""

def metDic(method):
    global methodDic
    if method in methodDic and methodDic[method][1] ==0:
        methodDic[method][1] = 1
        return methodDic[method][0]
    else:
        return ""

def objDic(obj,attr):
    global objectDic
    if obj in objectDic:
        objectDic[obj].append(attr)
    else:
        objectDic[obj] = attr
    return

def iftrans(args):
    if not args:
        return ""
    for i in range(0,len(args)):
        if isinstance(args, str):
            return args
        if isinstance(args[0], list ):
            if len(args) == 1:
                return trans(args[0])
            else:
                return trans(args[0])+param(args[1])
        else:
            if(len(args)<3):
                return ""
            if(i==2):
                def write():
                    exp = ""
                    global dic
                    assign = trans(args[i+1])
                    if assign[0] == '\n':
                        args[3][2][1] = args[i][1:(len(args[i])-1)]
                        return trans(args[i+1])
                    else:
                        vardic(args[i][1:(len(args[i])-1)])
                        exp += "(= " + args[i][1:(len(args[i])-1)]+"_"+str(dic.get(args[i][1:(len(args[i])-1)]))+ " " + assign+")"
                        return exp
                def putField():
                    return "(= " + "(select " + trans(args[i])+" "+ trans(args[i+1])+") "+ trans(args[i+2])+")"
                def ifelse():
                    exp = ""
                    for j in args[i]:
                        exp += "( => " + trans(args[i-1])+" "+iftrans(j)+")"
                    for j in args[i+2]: 
                        exp += "( => ( not " + trans(args[i-1])+") "+iftrans(j)+")"
                    return exp
                def notDefined():
                    return trans(args)
                option = {'J$.W':write,'J$.P':putField, 'if':ifelse}
                return option.get(args[i-2],notDefined)()
            else:
                continue

def trans(args):
    if not args:
        return ""
    for i in range(0,len(args)):
        if isinstance(args, str):
            return args
        if isinstance(args[0], list ):
            if len(args) == 1:
                return trans(args[0])
            else:
                return trans(args[0])+param(args[1])
        else:
            if(len(args)<3):
                return ""
            if(i==2):
                def unary():
                    if(args[i][1:(len(args[i])-1)]=='+' or args[i][1:(len(args[i])-1)]=='-'):
                        return trans(args[i+1])
                    else:
                        return "("+args[i][1:(len(args[i])-1)]+" "+trans(args[i+1])+")"
                def binary():
                    return "("+args[i][1:(len(args[i])-1)]+" "+trans(args[i+1])+" "+trans(args[i+2])+")"
                def condition():
                    return trans(args[i])
                def read():
                    global dic
                    return trans(args[i][1:(len(args[i])-1)])+"_"+str(dic.get(args[i][1:(len(args[i])-1)]))
                def write():
                    exp = ""
                    global dic
                    tempDic = copy.deepcopy(dic)
                    assign = trans(args[i+1])
                    if assign:
                        if assign[0] == '\n\n':
                            dic = copy.deepcopy(tempDic)
                            args[3][2][1] = args[i][1:(len(args[i])-1)]
                            return trans(args[i+1])
                        else:
                            vardic(args[i][1:(len(args[i])-1)])
                            exp += "(assert (= " + args[i][1:(len(args[i])-1)]+"_"+str(dic.get(args[i][1:(len(args[i])-1)]))+ " " + assign+"))"
                            return exp
                    else:
                        return ""
                def initial():
                    vardic(args[i][1:(len(args[i])-1)])
                    return ""
                def getField():
                    def length():
                        return "(str.len " + trans(args[i])+")"
                    def noField():
                        return "(select " + trans(args[i])+" "+ trans(args[i+1])+")"
                    attr = {'length':length}
                    if isinstance(args[i+1], list):
                        return attr.get(trans(args[i+1]),noField)()
                    else:
                        return attr.get(args[i+1][1:(len(args[i+1])-1)],noField)()
                def putField():
                    #objDic(trans(args[i]),trans(args[i+1]))
                    assign = trans(args[i+2])
                    global dic
                    tempDic = copy.deepcopy(dic)
                    if assign:
                        if assign[0] == '\n\n':
                            dic = copy.deepcopy(tempDic)
                            args[4][2][1] = args[i+1]
                            return trans(args[i+2])
                        else:
                            return "(assert (= " + "(select " + trans(args[i])+" "+ trans(args[i+1])+") "+ trans(args[i+2])+"))"
                    else:
                        return ""
                def literal():
                    if args[i]:
                        if isinstance(args[i][0],list):
                            exp = ""
                            for j in args[i]:
                                exp += trans(j) + '\n'
                            return exp
                        else:
                            return trans(args[i])
                    else:
                        return ""
                def method():
                    def substring():
                        return "(str.substr " + trans(args[i])
                    def indexOf():
                        return "(str.indexof "+ trans(args[i])
                    def noMethod():
                        return "(" +trans(args[i+1][1:(len(args[i+1])-1)])+" "+trans(args[i])
                    attr = {'indexOf':indexOf,'substring':substring}

                    if isinstance(args[i+1], list):
                        methodName = trans(args[i+1])
                    else:
                        methodName = args[i+1][1:(len(args[i+1])-1)]
                    exp = ""
                    met = metDic(methodName)
                    if(met):
                        print(met)
                    exp += attr.get(methodName,noMethod)()
                    return exp
                def fun():
                    def noFun():
                        return "(" + trans(args[i])
                    attr = {}
                    if isinstance(args[i+1], list):
                        return attr.get(trans(args[i+1]),noFun)()
                    else:
                        return attr.get(args[i+1][1:(len(args[i+1])-1)],noFun)()
                def forloop():
                    global dic
                    exp = ""
                    if args[i] == 'in':
                        for j in range(10):
                            iterExp = ""
                            vardic(args[i-1])                       
                            iterExp += "(assert (= (select " + trans(args[i+1]) + " " + str(j) + ") " + args[i-1] + "_"+str(dic.get(args[i-1])) + " ))\n"
                            for k in args[i+2]:
                                iterExp += trans(k)+"\n"
                            exp += iterExp
                    else:
                        exp +=  trans(args[i-1])
                        for j in range(10):
                            iterExp = ""                    
                            for k in args[i+2]:
                                iterExp += trans(k)+"\n"
                            iterExp +=  trans(args[i+1]) + '\n'
                            exp += iterExp 
                    return exp
                def ifelse():
                    exp = ""
                    for j in args[i]:
                        con = trans(args[i-1])
                        if(con):
                            exp += "(assert ( => " + trans(args[i-1])+" "+iftrans(j)+"))"+"\n"
                    for j in args[i+2]:
                        if(con):
                            exp += "(assert ( => ( not " + trans(args[i-1])+") "+iftrans(j)+"))"+"\n"
                    return exp

                def defineFun():
                    exp = "\n"
                    for j in args[i+1]:
                        iterExp = trans(j)
                        if 'returnexp' in iterExp:
                            if(args[i-1]):
                                exp += "(define-fun " + args[i-1] + " ("
                                for k in args[i]:
                                    exp += "(" + k +"_"+str(dic.get(k)) + " String)"
                                exp += ") String " + iterExp.replace("returnexp","") + ")"
                            else:
                                exp += "(define-fun " + "hahaha" + " ("
                                for k in args[i]:
                                    exp += "(" + k +"_"+str(dic.get(k)) + " String)"
                                exp += ") String " + iterExp.replace("returnexp","") + ")"
                        else:
                            exp += iterExp + '\n'                               
                    return exp
                def ret():
                    return trans(args[i]) + 'returnexp'

                def notDefined():
                    return trans(args[i])
                def ignore():
                    return ""
                option = {'J$.U':unary, 'J$.B':binary, 'J$.C':condition, 'J$.R':read, 'J$.W':write, 'J$.N':initial,
                            'J$.G':getField, 'J$.P':putField, 'J$.T':literal, 'J$.M':method, 'J$.F':fun, 'for':forloop,
                            'J$.Fe':ignore, 'J$.Ex':ignore, 'if':ifelse, 'J$.Rt':ret,'function':defineFun}
                return option.get(args[i-2],notDefined)()
            else:
                continue


def parse_args(cur, flag):
    args = []
    if js[cur:cur+3] == "for":
        args, cur = parse_for(cur)
        return args, cur
    if js[cur:cur+4] == "if (":
        args, cur = parse_if(cur)
        return args, cur
    if js[cur:cur+9] == "function ":
        args, cur = parse_func(cur)
        return args, cur
    sym = js[cur+3:cur+5]
    if sym in ("X1") and flag == 1:
        return [], -1
    left_bracket = 0
    right_bracket = 0
    left_brace = 0
    right_brace = 0
    check = False
    arg = ""
    gg = 0
    #if js[cur:cur+13] == "J$.T(37689, {":
        #gg = 1
    while left_bracket != right_bracket or left_brace != right_brace or check == False:
        #if gg == 1:    
            #print(left_bracket, right_bracket, js[cur])
        if js[cur:cur+9] == "function ":
            arg, cur = parse_func(cur)
            args.append(arg)
            arg = ""
            continue
        if sym == "T(" and (js[cur: cur+3] in (", {", ", [")):
            args.append(arg)
            arg, cur = parse_obj(cur+2)
            args.append(arg)
            arg = ""
            continue
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None and len(args) != 0:
            arg, cur = parse_args(cur, flag)
            if cur == -1:
                return arg, cur
            args.append(arg)
            arg = ""
            continue
        if js[cur] == "(":
            if check == False:
                args.append(arg)
                arg = ""
            left_bracket += 1
            #arg = re.sub(r"\n *", "", arg)
            #args.append(arg)
            #arg = ""
            if check == True:
                arg += js[cur]
            check = True
            cur += 1
            continue
        if js[cur] == ")":
            right_bracket += 1
            #arg = re.sub(r"\n *", "", arg)
            #args.append(arg)
            #arg = ""
            arg += js[cur]
            cur += 1
            continue
        if js[cur] == "{":
            check = True
            left_brace += 1
            arg = ""
            cur += 1
            continue
        if js[cur] == "}":
            right_brace += 1
            arg = ""
            cur += 1
            continue
        if js[cur] == " ":
            cur += 1
            continue
        if js[cur] == ",":
            arg = re.sub(r"\n *", "", arg)
            args.append(arg)
            arg = ""
            cur += 1
            continue
        arg += js[cur]
        #print(arg)
        cur += 1
        #print(args)
    args.append(arg[:-1])
    args = list(filter(("").__ne__, args))
    if sym in ("F(", "M("):
        call , cur = parse_args(cur, 0)
        args = [args] + [call]
   #  if(args):
        # if args[0] == "J$.T":
    #print(args)
    return args, cur

def parse_for(cur):
    if js[cur+14:cur+16] == "in":
        args = ["for", "J$._tm_p", "in"]
    else:
        args = ["for"]
    left_bracket = 0
    right_bracket = 0
    check = False
    end = 0
    while left_bracket != right_bracket or check == False:
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
            end = 0;
            arg, cur = parse_args(cur, 0)
            args.append(arg)
            arg = ""
            end = 1
            continue
        if js[cur] == ";" and end == 0:
            args.append([])
            end = 1
        if js[cur] == "(":
            check = True
            left_bracket += 1
        if js[cur] == ")":
            right_bracket += 1
        cur += 1
    left_brace = 0
    right_brace = 0
    check = False
    loop_code = []
    while left_brace != right_brace or check == False:
        if js[cur:cur+3] == "for":
            arg, cur = parse_for(cur)
            loop.code.append(arg)
            arg = ""
            continue
        if js[cur:cur+2] == "if":
            arg, cur = parse_if(cur)
            loop_code.append(arg)
            arg = ""
            continue
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
            start = cur
            arg, cur = parse_args(cur, 1)
            if cur == -1:
                cur = start+5
                arg = ""
                continue
            loop_code.append(arg)
            arg = ""
            continue
        if js[cur] == "{":
            check = True
            left_brace += 1
        if js[cur] == "}":
            right_brace += 1
        cur += 1
    args.append(loop_code)
    args = list(filter(("").__ne__, args))
    return args, cur
   
def parse_if(cur):
    gg = 0
    if js[cur:cur+15] == "if (J$.X1(37953":
        gg = 1
    args = ["if"]
    left_bracket = 0
    right_bracket = 0
    check = False
    #print(js[cur:cur+100])
    while left_bracket != right_bracket or check == False:
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
            arg, cur = parse_args(cur, 0)
            args.append(arg)
            arg = ""
            continue
        if js[cur] == "(":
            check = True
            left_bracket += 1
            cur += 1
            continue
        if js[cur] == ")":
            right_bracket += 1
            cur += 1
            continue
        cur += 1
    if_code = []
    no_bracket = 1
    if js[cur+1] == "{":
        no_bracket = 0
        left_brace = 0
        right_brace = 0
        check = False
        while left_brace != right_brace or check == False:
            if js[cur:cur+2] == "if":
                arg, cur = parse_if(cur)
                if_code.append(arg)
                arg = ""
                continue
            if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
                start = cur
                arg, cur = parse_args(cur, 1)
                if cur == -1:
                    cur = start+5
                    arg = ""
                    continue
                if_code.append(arg)
                arg = ""
                continue
            if js[cur] == "{":
                check = True
                left_brace += 1
                cur += 1
                continue
            if js[cur] == "}":
                right_brace += 1
                cur += 1
                continue
            if js[cur:cur+8] == "continue":
                if_code.append("continue")
                cur += 1
                continue
            if js[cur:cur+5] == "break":
                if_code.append("break")
                cur += 1
                continue
            cur += 1
    else:
        while js[cur]!="\n":
            cur = cur+1
        cur = cur+1
        while(js[cur]!="\n"):
            if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
                arg, cur = parse_args(cur, 0)
                if_code.append(arg)
                arg = ""
                continue
            if js[cur:cur+8] == "continue":
                if_code.append("continue")
                cur += 1
                continue
            if js[cur:cur+5] == "break":
                if_code.append("break")
                cur += 1
                continue
            cur += 1
        cur += 1
    if_code = list(filter(("").__ne__, if_code))
    args.append(if_code)
    args.append("else")
    else_code = []
    if no_bracket == 0:
        if js[cur+1:cur+5] == "else":
            cur += 5
            left_brace = 0
            right_brace = 0
            check = False
            if js[cur+1] == "{":
                while left_brace != right_brace or check == False:
                    if js[cur:cur+2] == "if":
                        arg, cur = parse_if(cur)
                        else_code.append(arg)
                        arg = ""
                        continue
                    if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
                        start = cur
                        arg, cur = parse_args(cur, 1)
                        if cur == -1:
                            cur = start+5
                            arg = ""
                            continue
                        else_code.append(arg)
                        arg = ""
                        continue
                    if js[cur] == "{":
                        check = True
                        left_brace += 1
                        cur += 1
                        continue
                    if js[cur] == "}":
                        right_brace += 1
                        cur += 1
                        continue
                    if js[cur:cur+8] == "continue":
                        else_code.append("continue")
                        cur += 1
                        continue
                    if js[cur:cur+5] == "break":
                        else_code.append("break")
                        cur += 1
                        continue
                    cur += 1
            elif js[cur+1:cur+3] == "if":
                arg, cur = parse_if(cur+1)
                else_code.append(arg)
                arg = ""
    else:
        buf = io.StringIO(js[cur:])
        next_line = buf.readline()
        n = next_line.find("else")
        if n != -1:
            cur += len(next_line)   
            while(js[cur]!="\n"):
                if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
                    arg, cur = parse_args(cur, 0)
                    else_code.append(arg)
                    arg = ""
                    continue
                if js[cur:cur+8] == "continue":
                    else_code.append("continue")
                    cur += 1
                    continue
                if js[cur:cur+5] == "break":
                    else_code.append("break")
                    cur += 1
                    continue
                cur += 1
            cur += 1
    else_code = list(filter(("").__ne__, else_code))
    args.append(else_code)
    args = list(filter(("").__ne__, args))
    #print(args)
    return args, cur

def parse_obj(cur):
    arg = ""
    args = []
    sym1 = js[cur]
    if sym1 == "{":
        sym2 = "}"
        #args = {}
    if sym1 == "[":
        sym2 = "]"
        #args = []
    left = 0
    right = 0
    check = False
    key = ""
    while left != right or check == False:
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
            arg, cur = parse_args(cur, 0)
            #if sym1 == "{":
                #args[key] = arg
            #if sym1 == "[":
            args.append(arg)
            arg = ""
            continue
        if js[cur] == sym1:
            check = True
            left += 1
            cur += 1
            continue
        if js[cur] == sym2:
            if sym1 == "[":
                args.append(arg)
            arg = ""
            right += 1
            cur += 1
            continue
        if js[cur] == ":":
            #key = arg
            arg = ""
            cur += 1
            continue
        if js[cur] in (" ", "\n"):
            cur += 1
            continue
        if js[cur] == ",":
            if sym1 == "[":
                args.append(arg)
            arg = ""
            cur += 1
            continue
        arg += js[cur]
        cur += 1
    if sym1 == "[":
        args = list(filter(("").__ne__, args))
    return args, cur

def parse_func(cur):
    args = ['function']
    left_bracket = 0
    right_bracket = 0
    check = False
    argss = []
    arg = ""
    if js[cur+9] != "(":
        n = js[cur:].find("(")
        args.append(js[cur+9:cur+n])
        cur += n
    else:
        cur += 9
        args.append([])
    while left_bracket != right_bracket or check == False:
        if js[cur] == "(":
            check = True
            left_bracket += 1
            argss.append(arg)
            arg = ""
            cur += 1
            continue
        if js[cur] == ")":
            right_bracket += 1
            argss.append(arg)
            arg = ""
            cur += 1
            continue
        if js[cur] == " ":
            cur += 1
            continue
        if js[cur] == ",":
            argss.append(arg)
            arg = ""
            cur += 1
            continue
        arg += js[cur]
        cur += 1
    argss = list(filter(("").__ne__, argss))
    args.append(argss)
    left_brace = 0
    right_brace = 0
    #print(args)
    func_code = []
    check = False
    arg = ""
    while left_brace != right_brace or check == False:
        if js[cur:cur+9] == "function ":
            arg, cur = parse_func(cur)
            func_code.append(arg)
            arg = ""
            continue
        if js[cur:cur+2] == "if":
            arg, cur = parse_if(cur)
            func_code.append(arg)
            arg = ""
            continue
        if js[cur:cur+5] == "for (":
            arg, cur = parse_for(cur)
            func_code.append(arg)
            arg = ""
            continue
        if re.match("J\$\.[A-Z]", js[cur:cur+4]) is not None:
            start = cur
            arg, cur = parse_args(cur, 1)
            if cur == -1:
                cur = start+5
                arg = ""
                continue
            func_code.append(arg)
            arg = ""
            continue
        if js[cur] == "{":
            check = True
            left_brace += 1
        if js[cur] == "}":
            right_brace += 1
        cur += 1
        func_code = list(filter(("").__ne__, func_code))
    args.append(func_code)
    return args, cur

result = ""

with open(sys.argv[1], 'r') as f:
    js = f.readline()
    js = f.read()
    cur = 0
    while(1):
        pos = [m.start(0) for m in re.finditer(r"J\$\.[A-Z]|for \(|if \(|function ", js[cur:])]
        #pos = [m.start(0) for m in re.finditer(r"function ", js[cur:])]
        if len(pos) != 0:
            cur = pos[0]+cur
            start = cur
            #print(js[cur:cur+50])
            #print("jizz")
            args, cur = parse_args(cur, 1)
            if cur == -1:
                cur = start+5
                continue
            print(args, flush=True)
            #print (start, cur)
            res = trans(args)
            if(res):
                result += res + '\n'
        else:
            break

print(declare, end='')
print(result, end='')
