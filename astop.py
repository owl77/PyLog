
import parser
import tokenizer
import copy

def Free(ast,varnames):
 if type(ast).__name__=="Leaf":
   if not ast.name in varnames:
    ast.free = True
    return ast
   else:
    ast.free = False
    return ast
 else:
  if not ast.operator.name in ["forall","exists","unique","lambda","extension"]:
   oldchildren = ast.children
   ast.children = [Free(x,varnames) for x in oldchildren]
   return ast
  else:
   newnames = varnames + [ast.operator.variable.name]
   oldchildren = ast.children
   ast.children = [Free(x,newnames) for x in oldchildren]
   return ast


def VarSubstitution(ast,oldname,freshname):
 if type(ast).__name__=="Leaf":
  if ast.free ==True and ast.name == oldname:
   ast.name = freshname
   return ast
  else:
   return ast
 else:
  oldchildren = ast.children
  ast.children=[VarSubstitution(x,oldname,freshname) for x in oldchildren]
  return ast

def Passing(list, func, n):
 if len(list)==0:
  return [[],n]
 if len(list)==1:
  return [[func(list[0],n)[0]], func(list[0],n)[1]]
 else:
  aux = func(list[0],n)
  aux2 = Passing(list[1:], func, aux[1])
  return [[aux[0]]+ aux2[0], aux2[1]]



def PredicatePosition(ast,predicatename,n):
 if type(ast).__name__=="Constructor" and ast.operator.name ==predicatename:     
   ast.operator.pos = n
   return [ast, n+1]
 else:
  if type(ast).__name__=="Leaf":
   return [ast, n]
  else:
   aux = Passing(ast.children, lambda x,y: PredicatePosition(x,predicatename,y), n)
   ast.children = aux[0]
   return [ast,aux[1]]


def NegationExpand(ast):
 if type(ast).__name__=="Leaf":
  return ast    
 if type(ast).__name__=="Constructor" and ast.operator.name == "neg":
     
   neg = parser.Formula(tokenizer.Tokenize("_|_"))
   form = NegationExpand(ast.children[0])
   imp = parser.SimpleCons(parser.operators)(["->"])
   aux = parser.Constructor(imp,imp.type,[form,neg])      
   return aux
 else:
   oldchildren = ast.children
   ast.children = [NegationExpand(x) for x in oldchildren]
   if len(ast.children) == 2:
     ast.left = ast.children[0]
     ast.right = ast.children[1]         
   return ast
 
 
def ExpandEquiv(ast):
 if type(ast).__name__=="Leaf":
  return ast    
 if type(ast).__name__=="Constructor" and ast.operator.name == "equiv":
   scope1 = parser.Printout(ast.children[0])
   scope2 = parser.Printout(ast.children[1])
   return parser.Formula(tokenizer.Tokenize("((" + scope1 +" -> "+ scope2 +") &  (" +scope2 + " -> "  + scope1 + "))"))
 else:
   return ast     

def CreateEquiv(ast):
   if type(ast).__name__=="Leaf":
    return None    
   if type(ast).__name__=="Constructor" and ast.operator.name == "&":
    
    leftimp = ast.children[0]
    rightimp = ast.children[1]
    if type(leftimp).__name__=="Constructor" and leftimp.operator.name == "->"  and  type(rightimp).__name__=="Constructor" and rightimp.operator.name == "->":
         
      left1 = leftimp.children[0]
      left2 = leftimp.children[1]
      right1 = rightimp.children[0]
      right2 = rightimp.children[1]
      if Equals(left1,right2) and Equals(left2,right1):
        
        return parser.Formula(tokenizer.Tokenize("(" + parser.Printout(left1)  + " equiv " +  parser.Printout(right1) +")" ))  
      
       
                   
       

def BoundVariableChange(ast,oldname,newname):
 if type(ast).__name__=="Leaf":
  return ast
 else:
  if ast.operator.name in ["exists","forall","unique","lambda","extension"]:
   if ast.operator.variable.name==oldname:
    ast.operator.variable.name=newname
    aux = [VarSubstitution(Free(x,[]),oldname,newname) for x in ast.children]
    ast.children = [BoundVariableChange(x,oldname,newname) for x in aux]
    return ast
   else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast
  else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast
 

def Numeric(ast,n):
 if type(ast).__name__=="Leaf":
  return ast
 else:
  if ast.operator.name in ["exists","forall","lambda","extension","unique"]:
   var = ast.operator.variable.name
   ast.operator.variable.name = str(n)
   aux = VarSubstitution(Free(ast.children[0],[]), var, str(n)) 
   ast.children = [Numeric(aux, n+1)]
   return ast
  else:
   aux = [Numeric(x,n) for x in ast.children]
   ast.children = aux
   return ast

def Equals(ast1,ast2):
  a1 = copy.deepcopy(ast1)
  a2 = copy.deepcopy(ast2)    
  aux1 = Numeric(a1,0)
  aux2 = Numeric(a2,0)
  return parser.Printout(aux1) == parser.Printout(aux2)


def FreeEquiv(ast1,ast2):
 if type(ast1).__name__=="Leaf":
  if ast1.free!=ast2.free:
    return False 
 else:
   for x in range(0,len(ast1.children)):
     if FreeEquiv(ast1.children[x],ast2.children[x])!=True:
      return False
  
 return True
    


def Position(ast,exp,n):
 
 
 if Equals(ast,exp) and FreeEquiv(ast,exp):
       
  if type(ast).__name__=="Leaf":    
   ast.pos = n
  else:
   ast.operator.pos = n     
  return [ast, n+1]
 else:
  if type(ast).__name__=="Leaf":
   return [ast, n]
  else:
   kinder = copy.deepcopy(ast.children)      
   aux = Passing(kinder, lambda x,y: Position(x,exp,y), n)
   ast.children = aux[0]
   return [ast,aux[1]]


def BasicSubstitution(ast,old,fresh):
 if type(ast).__name__=="Leaf":
    if ast.free!=True:
      return ast    
 if Equals(ast,old):     
   return fresh
 if type(ast).__name__=="Leaf":
  return ast
 else:
  oldchildren = ast.children
  ast.children=[BasicSubstitution(x,old,fresh) for x in oldchildren]
  if len(ast.children)==2:
    ast.left = ast.children[0]
    ast.right = ast.children[1]  
  return ast

def BasicSubstitutionByPosition(ast,old,fresh,positions):
    
 if Equals(ast,old):
   if ast.name=="constructor" and ast.operator.pos in positions:     
    return fresh
   if ast.name!="constructor" and ast.pos in positions:
     return fresh
 if type(ast).__name__=="Leaf":
  return ast
 else:
  oldchildren = ast.children
  ast.children=[BasicSubstitutionByPosition(x,old,fresh,positions) for x in oldchildren]
  if len(ast.children)==2:
    ast.left = ast.children[0]
    ast.right = ast.children[1]
  return ast


def GetPolyVars(ast):
 if type(ast).__name__ =="Leaf":
    if ast.type=="Formula":
     return [ast.name]
    else:
     return []
 else:     
  aux =[GetPolyVars(x) for x in ast.children]
  aux2 = []
  for x in aux:
   for y in x:
    aux2.append(y)
  return aux2       
     



def GetFreeVars(ast,typ):
 if type(ast).__name__== "Leaf":
  if ast.free==True and ast.type==typ:
   return [ast.name]
  else:
   return []
 else:
   aux =[GetFreeVars(x,typ) for x in ast.children]
   aux2 = []
   for x in aux:
    for y in x:
     aux2.append(y)
   return aux2
#this should preserve the order, useful for Bealer's logic.

  
def GetBindVars(ast):
 if type(ast).__name__=="Leaf":
  return []
 else:
  if ast.operator.name in ["exists","forall","unique","lambda","extension"]:
   aux3 = [ast.operator.variable.name]
  else:
   aux3=[]
  aux2 =[GetBindVars(x) for x in ast.children]
  for x in aux2:
   for y in x:
    aux3.append(y) 
  return aux3

def Substitution(ast,var,term):
  free = GetFreeVars(term,"Term")
  
  bind = GetBindVars(ast)
  
  subs = [x for x in bind if x in free]
  
  for y in subs:
   y2 = tokenizer.Fresh(parser.variables,tokenizer.alphabet)
   
   ast = BoundVariableChange(ast,y, y2)
   
   parser.variables.append(y2)
   
  return BasicSubstitution(ast,var,term)

def SubstitutionByPosition(ast,term1,term2,positions):
  free = GetFreeVars(term2,"Term")
  bind = GetBindVars(ast)
  subs = [x for x in bind if x in free]
  for y in subs:
   y2 = tokenizer.Fresh(parser.variables,tokenizer.alphabet)
   ast = BoundVariableChange(ast,y, y2)
   parser.variables.append(y2)
  return BasicSubstitutionByPosition(Position(ast,term1,0)[0],term1,term2,positions)



def MultiSub(form,oldnamelist,newtermlist):
 #must check for clashes    
 aux = form
 for k in range(0,len(oldnamelist)):  
  aux = Substitution(form,parser.Term(tokenizer.Tokenize(oldnamelist[k])) , newtermlist[k])
 return aux      

   

def ConceptExp(ast,conceptname,positions,definitions):
  if not type(ast).__name__=="Leaf":
   if ast.operator.name == conceptname and ast.operator.pos in positions:
    aux = ast.children
    aux2 = copy.deepcopy(definitions[conceptname]["formula"])
    aux3 = copy.deepcopy(definitions[conceptname]["arguments"])
    return MultiSub(aux2, aux3, aux)
   else:
    oldchildren = ast.children
    ast.children=[ConceptExp(x,conceptname,positions,definitions) for x in oldchildren]
    return ast
  else:
   return ast


def PreConceptSub(ast, conceptname,args,definitions):  
   aux2 = copy.deepcopy(definitions[conceptname]["formula"]) 
   aux3 = copy.deepcopy(definitions[conceptname]["arguments"])    
   aux = MultiSub(aux2, aux3,args)
  
   ast = Position(Free(ast,[]),Free(aux,[]),0)[0]
   
   return ast
   
def PostConceptSub(ast,conceptname,args,positions,definitions):  
   if type(ast).__name__=="Leaf":
     return ast   
   if ast.operator.pos in positions:  
     aux2 = [parser.Printout(a) for a in args]    
     return parser.Formula(tokenizer.Tokenize(conceptname+"(" +','.join(aux2)+ ")" ))   
   else:
     oldchildren = copy.deepcopy(ast.children)
     ast.children=[PostConceptSub( x , conceptname , args, positions,definitions) for x in oldchildren]
     return ast

def ConceptSub(ast,conceptname,args,positions,definitions):
 
 return PostConceptSub(PreConceptSub(ast,conceptname,args,definitions),conceptname,args,positions,definitions)    
     
