import parser
import tokenizer
import astop
import pickle
import copy
import os
import inspect

def Intersect(list1,list2):
 return [x for x in list1 if x in list2]
 
def PrintNumList(list):
 out = "[" 
 for x in list:
  out = out + str(x) + ","
 out1 = out[:len(out)-1]
 return out1 +"]"

 
def PrintStrList(list):
 out = "[" 
 for x in list:
  out = out + '"'+ str(x) + '"' + ","
 out1 = out[:len(out)-1]
 return out1 +"]"
  
 
  
class ProofElement:
  def __init__(self,name,dependencies,parameters,discharging,formula):
        self.name = name
        self.dependencies = dependencies
        self.parameters = parameters
        self.discharging = discharging
        self.formula = formula
        self.dischargedby = []
        self.pos = 0
        self.qed=False 
        self.comment=""

class ProofEnvironment:
 def __init__(self,proof,name):
       self.proof = proof
       self.name = name
       self.definitions = {}
       self.definitionequations = []
       self.axioms = []
       self.theorems = []
       self.log = []

 def CheckRange(self, dependencies):
       for dep in dependencies:
        if dep > len(self.proof):
         return False
       return True

 def GetTree(self,proofelement):
       out = [proofelement.pos-1]
       for dep in proofelement.dependencies:
         out = out + self.GetTree(self.proof[dep])
       return out

 def GetHyp(self,proofelement):
         if proofelement.name =="Hyp":
          return [proofelement.pos-1]
         out = []
         for dep in proofelement.dependencies:
          out = out + self.GetHyp(self.proof[dep])
         return out

 def CheckDischargedBy(self, hyp, proofelem):
       if len(self.proof[hyp].dischargedby) ==0:
         return False
       for h in self.proof[hyp].dischargedby:
         if h in self.GetTree(self.proof[proofelem]):
          return True
       return False

 def GetHypDep(self,proofelement):
       aux = []
       for  h in self.GetHyp(proofelement):
        if len(Intersect([x-1 for x in self.proof[h].dischargedby], self.GetTree(proofelement))) == 0:
         aux.append(h)
       return aux 


 def Hyp(self,formstring):
        form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring)))
        proofelement = ProofElement("Hyp",[],[],[], form)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Hyp(" + '"' + formstring + '"' + ")")
        return True
        

 def NewAx(self,formstring):
        form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring)))
        self.axioms.append(form)
        self.log.append("NewAx(" + +'"' +formstring + '"' +")")
        return True


 def AxInt(self,axnum):
        proofelement = ProofElement("AxInt",[],[],[], self.axioms[axnum])
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("AxInt(" + str(axnum) +")")
        return True 
 

 def EquivExp(self,up):
        proofelement = ProofElement("EquivExp",[],[],[], astop.ExpandEquiv(self.proof[up].formula))
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("EquivExp(" + str(up) +")")
        return True 
  

 def EquivConst(self,up):
        proofelement = ProofElement("EquivConst",[],[],[], astop.CreateEquiv(self.proof[up].formula))
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("EquivConst(" + str(up) +")")
        return True 
  
  

 def DefEqInt(self,axnum):
         proofelement = ProofElement("DefEqInt",[],[],[], self.definitionequations [axnum])
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("DefEqInt(" + str(axnum) +")")
         return True             

 def AddTheorem(self,formstring):
         form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring))) 
         self.theorems.append(form)
         return True


 def TheoremInt(self,axnum):
         proofelement = ProofElement("TheoremInt",[],[],[], self.theorems[axnum])
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("TheoremInt(" + str(axnum) +")")
         return True       
                
 def Qed(self,up):
      if len(self.GetHypDep(self.proof[up]))==0:
       self.proof[up].qed = True
       return True
      return False

 def AndInt(self,left,right):
  form = parser.Formula(tokenizer.Tokenize("("+parser.Printout(self.proof[left].formula)  + "&"+ parser.Printout(self.proof[right].formula)  + ")"))
  proofelement = ProofElement("AndInt",[left,right],[],[], form)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndInt(" +str(left) +","+str(right) + ")")
  return True


 def AndElimL(self,up):
  proofelement = ProofElement("AndElimL",[up],[],[], self.proof[up].formula.left)  
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndElimL(" + str(up) +")")
  return True

 def AndElimR (self,up):
  proofelement = ProofElement("AndElimR",[up],[],[], self.proof[up].formula.right)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndElimR(" + str(up) +")")
  return True

 def ImpElim (self, left,right):
  if self.proof[right].formula.operator.name =="->" and  astop.Equals(self.proof[right].formula.left ,self.proof[left].formula):
   proofelement = ProofElement("ImpElim",[left,right],[],[], self.proof[right].formula.right)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("ImpElim(" +str(left) +","+str(right) + ")")
   return True

 def ImpInt(self,up,dis):
  if not self.proof[dis].name=="Hyp":
   return None
  if not self.CheckDischargedBy(dis,up)==True:
    proofelement = ProofElement("ImpInt",[up],[],[], parser.Formula(tokenizer.Tokenize("("+parser.Printout(self.proof[dis].formula)+ "->"+
    parser.Printout(self.proof[up].formula)+ ")" )))
    proofelement.pos = len(self.proof) + 1
    self.proof[dis].dischargedby.append(proofelement.pos-1)
    self.proof.append(proofelement)
    self.log.append("ImpInt(" +str(up) +","+str(dis) + ")")
    return True

 def OrIntR(self, up,formstring):
    aux = astop.NegationExpand(Formula("(" + parser.Printout(self.proof[up].formula)+ " v " + formstring +")"  ))
    proofelement = ProofElement("OrIntR",[up],[],[], aux)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("OrIntR(" + str(up) + "," + '"' + formstring + '"' + ")")
    return True
    

 def OrIntL(self, up,formstring):
    aux = astop.NegationExpand(Formula("(" + formstring + " v " + parser.Printout(self.proof[up].formula)  +")"  ))
    proofelement = ProofElement("OrIntL",[up],[],[], aux)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("OrIntL(" + str(up) + "," + '"'+ formstring + '"' + ")")
    return True
        

 def OrElim(self, up, left, c1, right, c2):
  if left > c1 or right > c2:
    return 
  if not self.proof[left].name =="Hyp" or not self.proof[right].name =="Hyp":
    return         
  if astop.Equals(self.proof[c1].formula,self.proof[c2].formula):
    if self.proof[up].formula.operator.name=="v":
     if astop.Equals(self.proof[up].formula.children[0], self.proof[left].formula) and astop.Equals(self.proof[up].formula.children[1], self.proof[right].formula):         
      proofelement = ProofElement("OrElim",[up,left,c1,right,c2],[],[], copy.deepcopy(self.proof[c1].formula) )
      proofelement.pos = len(self.proof) + 1
      self.proof[left].dischargedby.append(proofelement.pos)
      self.proof[right].dischargedby.append(proofelement.pos)
      self.proof.append(proofelement)
      self.log.append("OrElim(" + str(up) + "," + str(left) + "," + str(c1) + "," + str(right) + "," + str(c2) + ")")
      return True
      
 def ForallElim (self, up,termstring):
   if self.proof[up].formula.operator.name=="forall":
    form = copy.deepcopy(self.proof[up].formula)   
    term = parser.Term(tokenizer.Tokenize(termstring))
    proofelement = ProofElement("ForallElim", [up],[term],[], astop.Substitution( astop.Free(form.children[0],[]) , form.operator.variable, term) )
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("ForallElim(" + str(up) +"," + '"' + termstring +'"' +")")
    return True

 def ExistsInst (self, up, newvar):
   if self.proof[up].formula.operator.name=="exists":
    form = copy.deepcopy(self.proof[up].formula)   
    term = parser.Term(tokenizer.Tokenize(newvar))
    proofelement = ProofElement("Hyp", [],[],[], astop.Substitution( astop.Free(form.children[0],[]) , form.operator.variable, term) )
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("ExistsInst(" + str(up) +"," + '"' + newvar +'"' + ")")
    return True         

 def ForallInt (self, up, variablestring, quantvarstring):
     if quantvarstring in parser.constants:
        return None
     if not quantvarstring in parser.variables:
         return None
     variable = parser.Term(tokenizer.Tokenize(variablestring))
     quantvar = parser.Term(tokenizer.Tokenize(quantvarstring))
     check = astop.GetFreeVars(astop.Free(self.proof[up].formula,[]),"Term")
     if quantvar.name in check:
       if quantvar.name != variablestring:    
        return None
     for h in self.GetHypDep(self.proof[up]):
      if variable.name in [x for x in astop.GetFreeVars(astop.Free(self.proof[h].formula,[]),"Term")]:
       return "Fail"            
       return None
     form = copy.deepcopy(self.proof[up].formula) 
     aux1 = astop.Substitution(form, variable, quantvar)
     parser.Printout(aux1)
     aux2 = parser.Formula(tokenizer.Tokenize("forall "+quantvar.name +"."+ parser.Printout(aux1) ))
     proofelement = ProofElement("ForallInt", [up],[variable,quantvar],[], aux2) 
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("ForallInt(" + str(up) + "," + '"' + variablestring +'"' +"," + '"' + quantvarstring +'"' + ")")
     return True
     
     


 def ExistsElim(self,exists, sub, concl, inststring):
  if not self.proof[exists].formula.operator.name=="exists":
   return None
  inst = Term(inststring) 
  body = copy.deepcopy(self.proof[exists].formula.children[0])
  var = copy.deepcopy(self.proof[exists].formula.operator.variable)
  if not astop.Equals(astop.Substitution(body,var,inst),self.proof[sub].formula):
   return None
  dep = [x for x in self.GetHypDep(self.proof[concl]) if x!= sub]
  for h in dep:
   aux = astop.GetFreeVars(astop.Free(self.proof[h].formula,[]),"Term")
   n = inst.name
   if n in aux:
    return None
  aux2 = astop.GetFreeVars(astop.Free(self.proof[exists].formula,[]),"Term"),
  if inst.name in aux2:
     return None
  aux3 = astop.GetFreeVars(self.proof[concl].formula,"Term")
  if inst.name in aux3:
     return None         
  proofelement = ProofElement("ExistsElim", [exists,sub,concl],[inst],[], self.proof[concl].formula)
  proofelement.pos = len(self.proof) +1
  self.proof[sub].dischargedby.append(proofelement.pos)
  self.proof.append(proofelement)
  self.log.append("ExistsElim(" + str(exists) + "," + str(sub) +"," + str(concl) + "," + '"' + inststring +'"' + ")")
  return True

 def ExistsInt(self,up,termstring,newvarname,places):
  if newvarname in parser.constants:
    return None    
  if not newvarname in parser.variables:
    return None     
  newvar = Term(newvarname)     
  term = Term(termstring)     
  aux = copy.deepcopy(self.proof[up].formula)
  form = astop.SubstitutionByPosition(aux, term, newvar, places)
  aux2 = parser.Printout(form)
  out = parser.Formula(tokenizer.Tokenize("exists " + newvar.name +"." + aux2))
  proofelement = ProofElement("ExistsInt", [up],[termstring,newvarname,places],[], out)
  proofelement.pos = len(self.proof) +1
  self.proof.append(proofelement)
  self.log.append("ExistsInt(" + str(up) + "," + '"' + termstring + '"'+ "," + '"' + newvarname + '"' + "," + PrintNumList(places) +")")
  return True


 def AbsI(self,up,formstring):
    if parser.Printout(self.proof[up].formula) =="_|_":
     proofelement = ProofElement("AbsI", [up],[formstring],[], Formula(formstring))
     proofelement.pos = len(self.proof) +1
     self.proof.append(proofelement)
     self.log.append("AbsI(" + str(up) + "," + '"' + formstring +'"'+")")
     return True
        
 def AbsC(self,abs,neghyp):
     if self.proof[neghyp].name =="Hyp" and type(self.proof[neghyp].formula).__name__ == "Constructor":
       if self.proof[neghyp].formula.operator.name=="->" and type(self.proof[neghyp].formula.right).__name__ =="Leaf":
          if self.proof[neghyp].formula.right.name=="_|_":
             if parser.Printout(self.proof[abs].formula)=="_|_":
                aux = copy.deepcopy(self.proof[neghyp].formula.left)
                proofelement = ProofElement("AbsC", [abs,neghyp],[],[], aux)
                proofelement.pos = len(self.proof) + 1
                self.proof[neghyp].dischargedby.append(proofelement.pos)
                self.proof.append(proofelement)
                self.log.append("AbsC(" + str(abs) + "," + str(neghyp) + ")")
                return True
                   

 def Symmetry(self, up):
  if self.proof[up].formula.operator.name =="=": 
   aux = copy.deepcopy(self.proof[up].formula)
   left = aux.left
   right = aux.right
   aux.left = right
   aux.right = left
   aux.children = [right,left]
   proofelement= ProofElement("Symmetry", [up],[],[], aux)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("Symmetry(" + str(up) + ")")
   return True

 
 def Identity (self, termstring):
      aux = parser.Formula(tokenizer.Tokenize("("+termstring +" = " + termstring + ")") )
      proofelement= ProofElement("Identity", [],[termstring], [],aux)
      proofelement.pos = len(self.proof) + 1
      self.proof.append(proofelement)
      self.log.append("Identity(" + '"' + termstring +'"' + ")")
      return True

 def EqualitySub(self, up, eq , places):
     form = copy.deepcopy(self.proof[up].formula)
     equa = copy.deepcopy(self.proof[eq].formula)
     aux1= equa.left
     aux2 = equa.right
     aux3 = astop.Position(form,aux1,0)
     aux = aux3[0]
     formula = astop.SubstitutionByPosition(aux,aux1,aux2,places)
     proofelement = ProofElement("EqualitySub" , [up,eq],[places], [],formula)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("EqualitySub(" + str(up) +"," + str(eq) + "," + PrintNumList(places) + ")")
     return True

 def ShowProof(self):
  n = 0     
  for  p in self.proof:
   if p.qed:      
    print(str(n)+". "+parser.PrettyPrintout(p.formula) +" "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]) + " Qed" )
   else:
    print(str(n)+". "+parser.PrettyPrintout(p.formula) +" "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]))      
   n = n + 1
   
 def ShowLog(self):
  n = 0        
  for l in self.log:
    print(str(n) + ". " + l)
    n = n + 1      
           
 def ShowLast(self):
   n = len(self.proof)
   print(str(n)+". "+parser.PrettyPrintout(p.formula) +" "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]))         
   
 def ShowAxioms(self):
  n = 0     
  for  p in self.axioms:
   print(str(n)+". "+parser.PrettyPrintout(p) +" ")
   n = n + 1
 def ShowTheorems(self):
  n = 0     
  for  p in self.theorems:
   print(str(n)+". "+parser.PrettyPrintout(p) +" ")
   n = n + 1
 def ShowDefEquations(self):
  n = 0     
  for  p in self.definitionequations:
   print(str(n)+". "+parser.PrettyPrintout(p) +" ")
   n = n + 1 
   
 def ShowDefinitions(self):      
  for x in self.definitions.keys():
    ast = Formula( "(" + x + "(" + ','.join(self.definitions[x]["arguments"]) +") equiv " + parser.Printout(self.definitions[x]["formula"]) +")" )
    print(parser.PrettyPrintout(ast))  
    
 def DefSub(self,up,conceptname,strargs,positions):
   args = [parser.Term(tokenizer.Tokenize(x)) for x in strargs]     
   ast = self.proof[up].formula
   defs = copy.deepcopy(self.definitions)
   aux = astop.ConceptSub(ast,conceptname,args,positions,defs)
   proofelement = ProofElement("DefSub" , [up],[conceptname,args,positions], [],aux)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("DefSub(" + str(up) + "," + '"' +conceptname +'"' +  "," + PrintStrList(strargs) + "," + PrintNumList(positions) + ")")
   return True
   
 def DefExp(self,up,conceptname,positions):
   ast = self.proof[up].formula
   ast = astop.PredicatePosition(ast,conceptname,0)[0]
   aux = astop.ConceptExp(ast,conceptname,positions,self.definitions)
   proofelement = ProofElement("DefExp" , [up],[conceptname,positions], [],aux)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("DefExp(" + str(up) + "," + '"' +conceptname + '"' + "," + PrintNumList(positions) +")")
   return True
    
 def NewDef(self, predname,args,formstring):
  self.AddPredicate(predname,len(args),True) 
  self.AddVariables(args)    
  form = astop.NegationExpand(Formula(formstring))  
  self.definitions[predname]={"formula":form, "arguments":args}
  self.log.append("NewDef(" + '"' +  predname+'"' + "," + PrintStrList(args) + "," + '"' + formstring+'"' + ")")
  return True 
 
 def NewDefEq(self,equationstring):
 
       
  equationstring = "("+equationstring +")"     
  if type(Formula(equationstring)).__name__!="Constructor":
     return None
  if Formula(equationstring).operator.name!="=":
      return None
  
  self.definitionequations.append(astop.NegationExpand(Formula(equationstring)))            
  self.log.append("NewDefEq(" + '"' + equationstring + '"' + ")")
  return True
 
 #Also DelDef, DelAx, DelTheorem, Del EqDef

 def PredSub(self,up,predicatename,arguments,formstring,positions):
  auxdef = { "arguments":arguments, "formula":Formula(formstring)}
  aux = astop.ConceptExp(copy.deepcopy(self.proof[up].formula),predicatename,positions,auxdef)
  proofelement = ProofElement("PredSub" , [up],[predicatename,arguments,formstring,positions], [],aux)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("PredSub(" + str(up) + "," + '"'+ predicatenmae +'"' +"," + PrintStrList(arguments) +"," + '"'+ formstring+'"' + "," + PrintNumList(positions) + ")")
  return True 
 
 def AddVariables(self,varlist): 
   parser.variables = parser.variables + varlist
   return True
 
 
 def AddConstants(self,varlist): 
   parser.constants.extend(varlist)
   parser.variables.extend(varlist)
   return True
 
 def AddPredicateVariables(self,varlist): 
   parser.predicatevariables = parser.predicatevariables + varlist
   return True
   
 def AddFunction(self,funcname,arity,prefix):
   parser.functions[funcname] = {"sourcetypes":parser.ArityToTypes(arity),"targettype":"Term", "prefix":prefix} 
   return True
   
 def AddPredicate(self, predname,arity,prefix):
   parser.predicates[predname] = {"sourcetypes":parser.ArityToTypes(arity),"targettype":"Formula","prefix":prefix}     
   return True
   
 def Save(self,name):    
   f = open(name,'wb')
   data = {"variables":parser.variables, "constants":parser.constants, "predicatevariables":parser.predicatevariables, 
   "functions": parser.functions,  "predicates":parser.predicates, "pretty":parser.pretty,  "proofenv":self}
   pickle.dump(data,f)
   f.close()
   return True 
   
   
 def UniqueElim(self,up,newbound):
  aux = copy.deepcopy(self.proof[up].formula)
  if aux.name =="constructor":
    if aux.operator.name=="unique":
     myvar = aux.operator.variable
     bod = aux.children[0]
     bod2 = parser.Printout(astop.Substitution(copy.deepcopy(bod), myvar, Term(newbound)))
     exis = Formula("exists " + myvar.name +"." + "(" + parser.Printout(bod) + " & " + "forall "+ newbound + ". (" + bod2  + " -> (" + newbound + " = " +myvar.name +") ) )")
     proofelement = ProofElement("UniqueElim" , [up],[], [],exis)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     return True
     
 def UniqueInt(self,up):
    aux = copy.deepcopy(self.proof[up].formula)
    if aux.name =="constructor":
      if aux.operator.name=="exists":
        var1 = aux.operator.variable
        if aux.children[0].name =="constructor":
         if aux.children[0].operator.name == "&":
            if aux.children[0].right.name =="constructor":
              if aux.children[0].right.operator.name =="forall":
                var2 = aux.children[0].right.operator.variable  
                if aux.children[0].right.children[0].name =="constructor":
                  if aux.children[0].right.children[0].operator.name=="->": 
                    left = aux.children[0].right.children[0].left
                    right = aux.children[0].right.children[0].right                      
                    if astop.Equals(right, Formula("(" + var2.name +" = "+ var1.name +")")) or astop.Equals(right, Formula("(" + var1.name +" = "+ var2.name +")")) :
                       if astop.Equals(left, astop.Substitution(copy.deepcopy(aux.children[0].left), var1, var2)):     
                         form = Formula("unique " + var1.name + "." + parser.Printout(aux.children[0].left))
                         proofelement = ProofElement("UniqueInt" , [up],[], [],form)
                         proofelement.pos = len(self.proof) + 1
                         self.proof.append(proofelement)
                         return True  
                  
 def ClassElim(self,up):
  if self.proof[up].formula.name=="constructor":
    if self.proof[up].formula.operator.name=="Elem":    
      if type(self.proof[up].formula.left).__name__=="Leaf":
        myvar = copy.deepcopy(self.proof[up].formula.left)  
        if self.proof[up].formula.right.name == "constructor":
         if self.proof[up].formula.right.operator.name =="extension":
            body = copy.deepcopy(self.proof[up].formula.right.children[0])
            boundvar = copy.deepcopy(self.proof[up].formula.right.operator.variable)           
            aux = Formula("( Set(" + parser.Printout(myvar) +") & "+ parser.Printout(astop.Substitution(body,boundvar,myvar)) + ")" )     
            proofelement = ProofElement("ClassElim" , [up],[], [],aux)
            proofelement.pos = len(self.proof) + 1
            self.proof.append(proofelement)
            self.log.append("ClassElim(" + str(up) + ")")
            return True
   
 def ClassInt(self,up,newvarname):
  form = self.proof[up].formula  
  newvar = Term(newvarname)   
  if form.name =="constructor":
      if form.operator.name=="&":
        if form.left.name=="constructor": 
         if form.left.operator.name=="Set":
           if form.left.children[0].name!="constructor":
             var = form.left.children[0]
             body = form.right
             aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("ClassInt" , [up],[newvarname], [],aux)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("ClassInt(" + str(up) + "," + '"' +newvarname +'"' + ")")
             return True            
   
        if form.right.name=="constructor": 
         if form.right.operator.name=="Set":
           if form.right.children[0].name!="constructor":
             var = form.right.children[0]
             body = form.left
             aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("ClassInt" , [up],[newvarname], [],aux)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("ClassInt(" + str(up) + "," + '"' + newvarname + '"' + ")")
             return True            
        
 
   
   
 def PolySub(self,up,polyvarname,formstring):
     form = copy.deepcopy(self.proof[up].formula)
     aux = astop.Substitution(form, Formula(polyvarname),Formula(formstring)) 
     proofelement = ProofElement("PolySub" , [up],[polyvarname,formstring], [],aux)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     return True   
 
      
 def LoadTheorem(self,name):
  global Proof    
  f = open(name,'rb')
  data = pickle.load(f)
  theorem = parser.Printout(data["proofenv"].proof[-1].formula)
  self.AddTheorem(theorem)
  f.close()
  return True
 
 def ViewTheorem(self,name):
  global Proof    
  f = open(name,'rb')
  data = pickle.load(f)
  theorem = name + " : "+ parser.PrettyPrintout(data["proofenv"].proof[-1].formula)
  f.close()
  return theorem
 
 def ViewTheory(self,name):
   dire = os.listdir(name)
   os.chdir(name)
   for t in dire:
    if t[0]!= '.':   
     print(self.ViewTheorem(t))
   os.chdir("..")     
   return True    
  
  
#shortcuts
  
 def FreeSub(self,up, freevar,instance):
  self.ForallInt(up,freevar,freevar)
  self.ForallElim(up+1,instance) 
  return True     
 
 def EquivJoin(self,left,right):
   self.AndInt(left,right)
   self.EquivConst(len(Proof.proof))
   return True
   
 def EquivLeft(self,up):
   self.EquivExp(up)
   self.AndElimL(len(Proof.proof))  
   return True
  
 def EquivRight(self,up):
   self.EquivExp(up)
   self.AndElimR(len(Proof.proof))  
   return True 
   
   
 def Undo(self):
   n = len(Proof.proof)
   Proof.proof.pop()
   for p in Proof.proof:
     if n in p.dischargedby:  
      p.dischargedby.remove(n)
   Proof.log.pop()       
   return True
           
def Formula(string):
   return parser.Formula(tokenizer.Tokenize(string))
def Term(string):
   return parser.Term(tokenizer.Tokenize(string))

Proof = ProofEnvironment([],"MyProof")
      
def Load(name):
 global Proof    
 f = open(name,'rb')
 data = pickle.load(f)
 Proof = data["proofenv"]
 parser.variables = data["variables"]
 parser.constants = data["constants"]
 parser.predicates = data["predicates"]
 parser.functions = data["functions"]
 parser.predicatevariables = data["predicatevariables"]
 parser.pretty = data["pretty"]
 f.close()
 return True

print("")
print("Welcome to PyLog 1.0") 
print("")
print("Natural Deduction Proof Assistant and Proof Checker")
print("")
print("(c) 2020  C. Lewis Protin")
print("")


def ShowLog():
 return Proof.ShowLog()
def GetHypDep(up):
 return Proof.GetHypDep(Proof.proof[up])      
def Hyp(form):
 return Proof.Hyp(form)            
def NewAx(formstring):
  return Proof.NewAx(formstring)      
def AxInt(axnum):
    return Proof.AxInt(axnum) 
def EquivExp(up):
    return Proof.EquivExp(up)
def EquivConst(up):
    return Proof.EquivConst(up)
def DefEqInt(axnum):
      return Proof.DefEqInt(axnum) 
def AddTheorem(formstring):
    return Proof.AddTheorem(formstring)     
def TheoremInt(axnum):
    return Proof.TheoremInt(axnum)         
def Qed(up):
     return Proof.Qed(up) 
def AndInt(left,right):
    return Proof.AndInt(left,right)
def AndElimL(up):
    return Proof.AndElimL(up)
def AndElimR (up):
    return Proof.AndElimR (up)
def ImpElim (left,right):
    return Proof.ImpElim (left,right)
def ImpInt(up,dis):
    return Proof.ImpInt(up,dis)
def OrIntR(up,formstring):
    return Proof.OrIntR(up,formstring)
def OrIntL(up,formstring):
    return Proof.OrIntL(up,formstring)
def OrElim(up, left, c1, right, c2):
    return Proof.OrElim(up, left, c1, right, c2)
def ForallElim(up,termstring):
    return Proof.ForallElim (up,termstring)
def ForallInt(up, variablestring, quantvarstring):
    return Proof.ForallInt(up, variablestring, quantvarstring)
def ExistsElim(exists, sub, concl, inststring):
    return Proof.ExistsElim(exists, sub, concl, inststring)
def ExistsInt(up,termstring,newvarname,places):
    return Proof.ExistsInt(up,termstring,newvarname,places)
def AbsI(up,formstring):
    return Proof.AbsI(up,formstring)
def AbsC(abs,neghyp):
    return Proof.AbsC(abs,neghyp) 
def Symmetry(up):
    return Proof.Symmetry( up)
def Identity ( termstring):
    return Proof.Identity ( termstring)  
def EqualitySub(up, eq , places):
    return Proof.EqualitySub(up, eq , places)
def ShowProof():
    return Proof.ShowProof()
def ShowLast():
    return Proof.ShowLast()
def ShowAxioms():
    return Proof.ShowAxioms()
def ShowTheorems():
    return Proof.ShowTheorems()
def ShowDefEquations():
    return Proof.ShowDefEquations()
def ShowDefinitions():      
    return Proof.ShowDefinitions()
def DefSub(up,conceptname,strargs,positions):
    return Proof.DefSub(up,conceptname,strargs,positions)
def DefExp(up,conceptname,positions):
    return Proof.DefExp(up,conceptname,positions)
def NewDef( predname,args,formstring):
    return Proof.NewDef( predname,args,formstring)
def NewDefEq(equationstring):
    return Proof.NewDefEq(equationstring)
def PredSub(up,predicatename,arguments,formstring,positions):
    return Proof.PredSub(up,predicatename,arguments,formstring,positions)
def AddVariables(varlist): 
    return Proof.AddVariables(varlist)
def AddConstants(varlist): 
    return Proof.AddConstants(varlist)
def AddPredicateVariables(self,varlist): 
    return Proof.AddPredicateVariables(self,varlist)
def AddFunction(funcname,arity,prefix):
    return Proof.AddFunction(funcname,arity,prefix)
def AddPredicate(predname,arity,prefix):
    return Proof.AddPredicate(predname,arity,prefix)
def Save(name):    
    return Proof.Save(name)
def ClassElim(up):
    return Proof.ClassElim(up)
def ClassInt(up,newvarname):
    return Proof.ClassInt(up,newvarname)
def PolySub(up,polyvarname,formstring):
    return Proof.PolySub(up,polyvarname,formstring)
def LoadTheorem(name):
    return Proof.LoadTheorem(name)
def FreeSub(up,freevar,instance):
    return Proof.FreeSub(up,freevar,instance) 
def ViewTheorem(name):
    return Proof.ViewTheorem(name)       
def Undo():
    return Proof.Undo()      
def EquivJoin(left,right):
    return Proof.EquivJoin(left,right)
def EquivLeft(up):
    return Proof.EquivLeft(up)
def EquivRight(up):
    return Proof.EquivRight(up)
def UniqueElim(up,newbound):    
    return Proof.UniqueElim(up)
def UniqueInt(up,newbound):    
    return Proof.UniqueInt(up)   
def ViewTheory(name):     
    return Proof.ViewTheory(name)
def ExistsInst (up, newvar):  
    return Proof.ExistsInst(up,newvar)  