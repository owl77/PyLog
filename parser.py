import copy
import tokenizer

class Leaf:
 def __init__(self,name,type):
  self.name = name
  self.signature = None
  self.type = type
  self.free = True
  self.pos = -1
  self.variable = None
 
  self.prefix =True
class Constructor:
  def __init__(self,operator, type,children):     
   self.name ="constructor"
   self.operator = operator
   self.type= type
   self.children = children
   self.binary = False
   self.left = None
   self.right = None
   if len(children)==2:
    self.binary =True
    self.left = children[0]
    self.right = children[1]

def Star(parser,separator):
 def out(exp):

     
     
     
  parse = parser(exp)      
  if parse!=None:
   return [parse]  
  if len(exp) < 3:
   return None
  if len( [x for x in separator if x in exp] ) == 0:
      return None
   
  length = len(exp) 
  for i in range(1,length-1):  
    if not exp[i] in separator:
     continue  
    
    

    par1 =  parser(exp[0:i])   
    
    if par1== None:
      continue
    #if not exp[i] in separator:
    # continue
    par2 =  Star(parser,separator)(exp[i+1:])
    if par2 == None:
      continue
    return [par1] + par2
    
        
        
        
    
    
 return out



def ListAst(listt, op, typee):
 if len(listt) < 2:
     return None
 if len(listt) == 2:
    return Constructor(Leaf(op, typee), typee  ,listt)
 else:
   return Constructor(Leaf(op, typee), typee  ,[listt[0], ListAst( listt[1:], op, typee )] )
   


def Star2(parser,separator):
 def out(exp):   
      
  if not separator in exp:
      return None
  

  if len(exp)<2:
    return None       
  if exp[0]!="(":
      return None
  if exp[len(exp)-1 ]!=")":
      return None
  trim = exp[1: len(exp)-1]
  aux = Star(parser,[separator])(trim)
  if aux == None:
      return None
 # aux2 = [TruePrintout(x) for x in aux]
 # aux3 = tokenizer.ParenthesisGen(aux2,separator)
 # aux4 = parser(tokenizer.Tokenize(aux3))          
  aux4 = ListAst(aux, separator, "Formula")
  # change "Formula" if needed 
 
  return aux4
 return out






def Binary(parser1,parser2, opparser):
 def out(exp):
  length = len(exp)     
  if length < 5:
   return None
  for i in range(2,length-2):
   opars = opparser([exp[i]])      
   if opars ==None:
     continue
   if  exp[0]!="(" or exp[length-1]!=")":
     continue
   par1 =  parser1(exp[1:i])
   if par1== None:
     continue
   par2 =  parser2(exp[i+1:length-1])
   if par2 == None:
      continue
   aux = Constructor(opars,opars.type,[par1,par2])
   if len(opars.signature)!=2:
     return None
   if opars.signature[0]!=aux.left.type or opars.signature[1]!= aux.right.type:
     return None
   return aux
 return out

def Operator(opparser, parser, separator,parenthesis):
 if parenthesis==True:
  def out(exp):
   if len(exp) < 4:
    return None
   for i in range(1,len(exp)-2):
       
    if  exp[i]!="(" or exp[len(exp)-1]!=")":
     continue
    opars =  opparser(exp[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(exp[i+1:len(exp)-1])
    if star == None:
     continue    
    
    if len(star)!=len(opars.signature):
      return 
    for i in range(0,len(star)):
     if star[i].type!=opars.signature[i]:
       return
    return Constructor(opars, opars.type,star)
    
  return out
 else:
  def out(exp):
   if len(exp) < 2:
    return 
   for i in range(1,len(exp)):
    aux1 = copy.deepcopy(exp)   
    opars = opparser(aux1[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(aux1[i:])
   
    if star == None:
        continue
    if len(star)!=len(opars.signature):
      return
    for i in range(0,len(star)):
      if star[i].type!=opars.signature[i]:
       return
    return Constructor(opars, opars.type,star)
    
  return out


def Or(parserlist):
 def out(exp):
  for i in range(0,len(parserlist)):
    par =  parserlist[i](exp) 
    if par!=None:
      return par
 return out


def Printout(ast):
 if type(ast).__name__=="Leaf":              
  return ast.name
 if type(ast).__name__=="Constructor":
  aux = [Printout(x) for x in ast.children]
  if ast.operator.name in ["square","diamond"]:
    return Printout(ast.operator) + " "+ aux[0]   
  if ast.binary == False or ast.operator.name not in ["v","&", "->","equiv"]:
   if ast.operator.name=="neg":
      return "neg " + aux[0]       
   if not ast.operator.name in ["exists","forall","unique","lambda","extension","quine"]: 
    if ast.operator.prefix == True :  
     return Printout(ast.operator) +"("+(",").join(aux)+")"
    if ast.operator.prefix == False:
      return "(" + aux[0]+ " "+Printout(ast.operator) + " "+aux[1]+")"
   else:
       
       
    if ast.operator.name!="quine":   
     return Printout(ast.operator) + " "+Printout(ast.operator.variable) + "." + aux[0]
    else:
     return "quine " + aux[0]  
  else:  
   return "(" + aux[0]+ " "+Printout(ast.operator) + " "+aux[1]+")"
   
   


def TruePrintout(ast):
    if type(ast).__name__=="Leaf":
     return ast.name
    if type(ast).__name__=="Constructor":
     aux = [TruePrintout(x) for x in ast.children]
     if ast.operator.name in ["square","diamond"]:
       return TruePrintout(ast.operator) + " "+ aux[0]   
     if ast.binary == False or ast.operator.name not in ["v","&", "->","equiv"]:
      if ast.operator.name=="neg":
         return "neg " + aux[0]       
      if not ast.operator.name in ["exists","forall","unique","lambda","extension","quine"]: 
        if ast.operator.name=="=":
           return "(" + aux[0]+ " "+TruePrintout(ast.operator) + " "+aux[1]+")"         
        else:
     
         return TruePrintout(ast.operator) +"("+(",").join(aux)+")"
       
      else:
       
       
       if ast.operator.name!="quine":   
        return TruePrintout(ast.operator) + " "+TruePrintout(ast.operator.variable) + "." + aux[0]
       else:
        return "quine " + aux[0]  
     else:  
      return "(" + aux[0]+ " "+TruePrintout(ast.operator) + " "+aux[1]+")"
   
   
   
   
 
def CheckNeg(ast):
 if ast.name=="constructor":
  if ast.operator.name=="->" and ast.right.name =="_|_":
     return True           
 return False  

pretty = {"Elem": " ε " , "square":"□", "diamond":"◇", "equiv":" <-> " ,"forall":"∀", "exists":"∃","unique":"∃¹", "lambda":"λ", "_|_": "┴"}



def prePrettyPrintout(ast):
 if CheckNeg(ast):
   return "¬" + prePrettyPrintout(ast.left)         
 if type(ast).__name__=="Leaf":
  if ast.name not in pretty.keys():     
   return ast.name
  else:
   return pretty[ast.name]
      
 aux = [prePrettyPrintout(x) for x in ast.children]
 #if ast.operator.name == "app" and type(ast.children[1]).__name__!="Leaf":
  #   if ast.children[1].operator.name == "orderedpair":
   #   return "(" + prePrettyPrintout(ast.children[1].left) + " "+ prePrettyPrintout(ast.children[0])+ " " +   prePrettyPrintout(ast.children[1].right)  + ")"  
 if ast.operator.name=="extension":
   return "{" + ast.operator.variable.name + ": " + prePrettyPrintout(ast.children[0])  +  "}"
 if ast.operator.name=="singleton":
    return "{" + prePrettyPrintout(ast.children[0])  +  "}"
 if ast.operator.name=="inv":
     return  "(" + prePrettyPrintout(ast.children[0]) + ")⁻¹"    
     
 if ast.operator.name =="domain":
   return "dom("   + prePrettyPrintout(ast.children[0]) + ")"
   
 if ast.operator.name =="Function":
   return "FUN("   + prePrettyPrintout(ast.children[0]) + ")"
 if ast.operator.name =="range":
   return "rg("   + prePrettyPrintout(ast.children[0]) + ")"
   
   
 if ast.operator.name =="OrderPreserving":
   return "OP("   + ','.join([prePrettyPrintout(x) for x in ast.children]) + ")"
   
 
 if ast.operator.name =="WellOrders":
   return "WO("  + ','.join([prePrettyPrintout(x) for x in ast.children])  + ")"  
 if ast.operator.name =="Section":
   return "Sec("  + ','.join([prePrettyPrintout(x) for x in ast.children])   + ")"
   
   
   
   
   
      
 if ast.operator.name=="pair":
    return "{" + prePrettyPrintout(ast.children[0])  + "," + prePrettyPrintout(ast.children[1]) + "}"  
 if ast.operator.name=="orderedpair":
    return "(" + prePrettyPrintout(ast.children[0])  + "," + prePrettyPrintout(ast.children[1]) + ")"  
  
  
 if ast.operator.name=="Arr":
    return "[" + prePrettyPrintout(ast.children[0])  + ": "+ prePrettyPrintout(ast.children[1])+" → "+ prePrettyPrintout(ast.children[2]) +"|"+prePrettyPrintout(ast.children[3])+"]"    
 
 if ast.operator.name=="Obj" or ast.operator.name=="TypeOf":
    return  prePrettyPrintout(ast.children[0]) + ":"+ prePrettyPrintout(ast.children[1]) 
 if ast.operator.name=="App" or ast.operator.name =="typeapp":
    return  prePrettyPrintout(ast.children[0]) + prePrettyPrintout(ast.children[1])        
   
 if ast.operator.name=="quine":
   return "[" + prePrettyPrintout(ast.children[0])  +  "]"   
 if ast.binary == True and ast.operator.prefix == False or ast.operator.name =="&":
  if ast.operator.name in pretty.keys():
   return "(" + prePrettyPrintout(ast.left) + pretty[ast.operator.name]+   prePrettyPrintout(ast.right)  + ")" 
  else:
    return "(" + prePrettyPrintout(ast.left) + " "+ ast.operator.name+ " " +   prePrettyPrintout(ast.right)  + ")"  
 if ast.operator.prefix == True  and ast.operator.name in pretty.keys() and not ast.operator.name in ["exists","forall","unique","lambda"] :  
   return pretty[ast.operator.name] + prePrettyPrintout(ast.children[0])
 if not ast.operator.name in ["exists","forall","unique","lambda"]: 
    return prePrettyPrintout(ast.operator) +"("+(",").join(aux)+")"
 else:
    if "forall" in pretty.keys():
        # for backwards compatibility in some theorems in which there was no pretty versions of quantifiers etc. 
     return pretty[ast.operator.name] + prePrettyPrintout(ast.operator.variable) + "." + aux[0]
    else:
      return prePrettyPrintout(ast.operator) + " " +prePrettyPrintout(ast.operator.variable) + "." + aux[0]  
 
def PrettyPrintout(ast): 
  aux = prePrettyPrintout(ast)
  if len(aux) < 101:
   if aux[0]=="(" and aux[len(aux)-1]==")":
    return aux[1:len(aux)-1]    
   else:
    return aux 
  else:
   a = aux[0:101]
   b = aux[101:]
   if len(b) < 101:
    if a[0] =="(":
     return a[1:] + "\n" + b[:len(b)-1]
    else:
     return a + b
   else:
    b = aux[101:202]
    c = aux[203:]
    if a[0] == "(":
     return a[1:] + "\n" + b[:101] + "\n" + c[:len(c)-1]
    else:
     return a + "\n" + b[:101] + "\n" + c[:len(c)-1]
     
      
    
     
binders = {"forall":{"sourcetypes":["Formula"], "targettype":"Formula"},"exists":{"sourcetypes":["Formula"], "targettype":"Formula"},
"unique":{"sourcetypes":["Formula"], "targettype":"Formula"}}

binderstoterm ={ "extension":{"sourcetypes":["Formula"], "targettype":"Term"}}

def BinderParser(binders,variableparser):
 def out(exp):     
  if len(exp) < 3 or len(exp) > 3:
   return None
  if exp[1] in constants:
    return None   
  if exp[0] in binders.keys() and variableparser([exp[1]])!=None and exp[2]==".":       
   aux = Leaf(exp[0], binders[exp[0]]["targettype"])
   aux.variable = variableparser([exp[1]])
   aux.signature = binders[exp[0]]["sourcetypes"]
   return aux
 return out




def Simple(list, type):
 def out(exp):
  if len(exp)!=1:
    return None
  if exp[0] in list:
   return Leaf(exp[0], type)
 return out
 

def SimpleCons(dic):
 def out(exp):
  if len(exp)!=1:
   return None
  if exp[0] in dic.keys():
   aux = Leaf(exp[0],dic[exp[0]]["targettype"])
   aux.signature = dic[exp[0]]["sourcetypes"]
   if len(aux.signature)== 2:
    aux.prefix = dic[exp[0]]["prefix"]            
   return aux
 return out

def Abs():
 def out(exp):
  if len(exp)!=1:
   return None
  if exp[0]=="_|_":
    return Leaf(exp[0], "Formula")
 return out
  
predicatevariables = ["A","B","C","D"] 
constants = []
variables = ["x","y","z","u","v","w" ,"x'","y'","z'","u'","v'","w'","f","g","h","r"]
functions = {"singleton":{"sourcetypes":["Term"],"targettype":"Term", "prefix":False }, "pair":{"sourcetypes":["Term","Term"],"targettype":"Term", "prefix":False } }
 

predicates = { "Elem":{"sourcetypes":["Term","Term"],"targettype":"Formula","prefix": False}, "Set":{"sourcetypes":["Term"],"targettype":"Formula","prefix":True} ,
"=":{"sourcetypes":["Term","Term"],"targettype":"Formula","prefix":False} }
operators = {"&":{"sourcetypes":["Formula","Formula"],"targettype":"Formula","prefix":False},
"v":{"sourcetypes":["Formula","Formula"],"targettype":"Formula","prefix":False},"equiv":{"sourcetypes":["Formula","Formula"],"targettype":"Formula","prefix":False},
"->":{"sourcetypes":["Formula","Formula"],"targettype":"Formula","prefix":False}}
modal = {"neg": {"sourcetypes":["Formula"],"targettype":"Formula"}}

def ArityToTypes(n):
 if n == 0:
  return []
 aux = ["Term"] + ArityToTypes(n-1)
 return aux     




#def Term(exp):
 #return Or([Simple(variables,"Term"), Binary(Term,Term,SimpleCons(functions)), Operator(SimpleCons(functions),Term,[","],True) ,
 #Operator(BinderParser(binderstoterm,Simple(variables,"Term")), Formula ,[","],False) ])(exp)    

#def Formula(exp):
# return Or([Abs(),Simple(predicatevariables,"Formula"), Operator(SimpleCons(predicates),Term, [","],True),Operator(SimpleCons(modal),Formula, [","],False),
#  Binary(Formula,Formula, SimpleCons(operators)), Binary(Term,Term, SimpleCons(predicates)),
#  Operator(BinderParser(binders,Simple(variables,"Term")), Formula ,[","],False), Star2(Formula,"&") ])(exp)

def Term(exp):
# if len(exp) == 0:
 #    return None    
 if len(exp) == 1 and exp[0] in variables:
    return Simple(variables,"Term")(exp)
 if exp[0] =="extension":
     return  Operator(BinderParser(binderstoterm,Simple(variables,"Term")), Formula ,[","],False)(exp)
 if exp[0] in functions.keys():
     
     return    Operator(SimpleCons(functions),Term,[","],True)(exp)
 return   Binary(Term,Term,SimpleCons(functions))(exp)           


def Formula(exp):
  if len(exp)== 1:
       if exp[0] == "_|_":
        return Leaf(exp[0], "Formula")
       return Simple(predicatevariables,"Formula")(exp)
       
  if exp[0] in ["forall", "exists"]:
      return Operator(BinderParser(binders,Simple(variables,"Term")), Formula ,[","],False)(exp)
     
  if exp[0] in predicates.keys():
      return Operator(SimpleCons(predicates),Term, [","],True)(exp)
   
  if exp[0] =="neg":
       return Operator(SimpleCons(modal),Formula, [","],False)(exp)
      
  test =   Binary(Formula,Formula, SimpleCons(operators))(exp)
  if test!= None:
          return test
  test =    Binary(Term,Term, SimpleCons(predicates))(exp)
  if test!=None:
         return test       
  test =    Star2(Formula,"&")(exp)
  return test
                                     
               
                      
    


def termtest(exp):
 return Term(tokenizer.Tokenize(exp))    

def formtest(exo):
  return Formula(tokenizer.Tokenize(exp))    

#also do category terms with category constructors
