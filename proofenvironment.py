import parser
import tokenizer
import astop
import pickle
import copy
import os
import inspect
import time

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
         out = list(set(out + self.GetTree(self.proof[dep])))
       return out






 def GetHyp(self,proofelement):
         if proofelement.name =="Hyp":
          return [proofelement.pos-1]
         out = []
         for dep in proofelement.dependencies:
          out = list(set(out + self.GetHyp(self.proof[dep])))
         return out

 def CheckDischargedBy(self, hyp, proofelem):
       if len(self.proof[hyp].dischargedby) ==0:
         return False
       for h in self.proof[hyp].dischargedby:
         if h-1 in self.GetTree(self.proof[proofelem]):
          return True
       return False

 #def GetHypDep(self,proofelement):
  #     aux = []
   #    for  h in self.GetHyp(proofelement):
    #    if len(Intersect([x-1 for x in self.proof[h].dischargedby], self.GetTree(proofelement))) == 0:
     #    aux.append(h)
      # return aux 
 
 def GetHypDep(self,proofelement):
     if proofelement.name =="Hyp":      
       return [proofelement.pos-1]
     aux = []
     for h in proofelement.dependencies:
        aux = aux + self.GetHypDep(self.proof[h]) 
     aux = list(set(aux))
     p = proofelement.pos
     aux2 = []
     for x in aux:
      if not p in self.proof[x].dischargedby:
        aux2.append(x)  
        
     return list(set(aux2))       
          
     
 
 
 
  

 def Hyp(self,formstring):
        a = parser.Formula(tokenizer.Tokenize(formstring))
        if a== None:
         print("Syntax Error.")
         return
        form = astop.NegationExpand(a)
        proofelement = ProofElement("Hyp",[],[],[], form)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Hyp(" + '"' + formstring + '"' + ")")
        
        return True
        

 def NewAx(self,formstring):
        if parser.Formula(tokenizer.Tokenize(formstring))== None:
         print("Syntax Error.")
         return
        form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring)))
        self.axioms.append(form)
   #     self.log.append("NewAx(" + '"' +formstring + '"' +")")
        
        return True


 def AxInt(self,axnum):
        if axnum > len(self.axioms)-1:
          print("Range exceeded.")
          return
        proofelement = ProofElement("AxInt",[],[],[], self.axioms[axnum])
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("AxInt(" + str(axnum) +")")
        
        return True 
 

 def EquivExp(self,up):
        if up > len(self.proof)-1:
          print("Range exceeded.")
          return
        proofelement = ProofElement("EquivExp",[up],[],[], astop.ExpandEquiv(self.proof[up].formula))
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("EquivExp(" + str(up) +")")
        
        return True 
  

 def EquivConst(self,up):
      if up > len(self.proof)-1:
        print("Range exceeded.")
        return
      a = astop.CreateEquiv(self.proof[up].formula)    
      if a!=None:
        proofelement = ProofElement("EquivConst",[up],[],[], a)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("EquivConst(" + str(up) +")")
        
        return True 
      else:
       print("Not an equivalence.")
       return
  

 def DefEqInt(self,axnum):
         if axnum > len(self.definitionequations)-1:
           print("Range exceeded.")
           return
         proofelement = ProofElement("DefEqInt",[],[],[], self.definitionequations [axnum])
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("DefEqInt(" + str(axnum) +")")
         
         return True             

 def AddTheorem(self,formstring):
         if parser.Formula(tokenizer.Tokenize(formstring))== None:
          print("Syntax Error.")
          return
         form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring))) 
         self.theorems.append(form)
         
         return True


 def TheoremInt(self,axnum):
         if axnum > len(self.theorems)-1:
           print("Range exceeded.")
           return
         proofelement = ProofElement("TheoremInt",[],[],[], self.theorems[axnum])
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("TheoremInt(" + str(axnum) +")")
         
         return True       
                
 def Qed(self,up):
      if up > len(self.proof)-1:
        print("Range exceeded.")
        return
      if len(self.GetHypDep(self.proof[up]))==0:
       self.proof[up].qed = True
       return True
      return False

 def AndInt(self,left,right):
     
  if left > len(self.proof)-1:
    print("Range exceeded.")
    return  
  if right > len(self.proof)-1:
    print("Range exceeded.")
    return       
  andop = parser.Leaf("&","Formula")
  andop.prefix = False
  andint = parser.Constructor(andop,"Formula", [self.proof[left].formula, self.proof[right].formula])       
     
#  form = parser.Formula(tokenizer.Tokenize("("+parser.Printout(self.proof[left].formula)  + "&"+ parser.Printout(self.proof[right].formula)  + ")"))
  proofelement = ProofElement("AndInt",[left,right],[],[], andint)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndInt(" +str(left) +","+str(right) + ")")
  
  return True


 def AndElimL(self,up):
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return     
  if self.proof[up].formula.name!="constructor":
     print ("Not a conjunction.")
     return None
  if self.proof[up].formula.operator.name!="&":
     print ("Not a conjunction.")
     return None
     
  proofelement = ProofElement("AndElimL",[up],[],[], self.proof[up].formula.left)  
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndElimL(" + str(up) +")")
  
  return True

 def AndElimR (self,up):
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return     
  if self.proof[up].formula.name!="constructor":
    print("Not a conjunction.")
    return None
  if self.proof[up].formula.operator.name!="&":
    print("Not a conjunction.")
    return None    
  proofelement = ProofElement("AndElimR",[up],[],[], self.proof[up].formula.right)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("AndElimR(" + str(up) +")")
 
  return True

 def ImpElim (self, left,right):
 
  if left > len(self.proof)-1:
    print("Range exceeded.")
    return 
  if right > len(self.proof)-1:
    print("Range exceeded.")
    return    
  if self.proof[right].formula.operator.name =="->" and  astop.Equals(self.proof[right].formula.left ,self.proof[left].formula):
   proofelement = ProofElement("ImpElim",[left,right],[],[], self.proof[right].formula.right)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("ImpElim(" +str(left) +","+str(right) + ")")
   
   return True
  else:
   print("Rule not applicable.") 
  
 def ImpInt(self,up,dis):
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return
  if dis > len(self.proof)-1:
    print("Range exceeded.")
    return         
  if not self.proof[dis].name=="Hyp":
   print("Cannot discharge a formula which is not an hypothesis.")
   return None
 # if not self.CheckDischargedBy(dis,up)==True:
 
 
  op = parser.Leaf("->","Formula")
  op.prefix = False
  left = self.proof[dis].formula
  right = self.proof[up].formula
  aux = parser.Constructor(op,"Formula", [left, right])
  
 
  proofelement = ProofElement("ImpInt",[up],[],[], aux) 
  
  
#  parser.Formula(tokenizer.Tokenize("("+parser.Printout(self.proof[dis].formula)+ "->"+
 # parser.Printout(self.proof[up].formula)+ ")" ))
  
  
   
  proofelement.pos = len(self.proof) + 1
  self.proof[dis].dischargedby.append(proofelement.pos) 
  self.proof.append(proofelement)
  self.log.append("ImpInt(" +str(up) +","+str(dis) + ")")
    
  return True

 def OrIntR(self, up,formstring):
    if up > len(self.proof)-1:
      print("Range exceeded.")
      return
    newf = Formula(formstring)
    if newf == None:
     print("Syntax Error.")
     return  
     
    formu = Formula("(A v B)")
   
    formu.children = [self.proof[up].formula,newf]
    formu.right =  newf
    formu.left = self.proof[up].formula 
   # aux = astop.NegationExpand(Formula("(" + parser.Printout(self.proof[up].formula)+ " v " + formstring +")"  ))
    proofelement = ProofElement("OrIntR",[up],[],[], astop.NegationExpand(formu))
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("OrIntR(" + str(up) + "," + '"' + formstring + '"' + ")")
    
    return True
    

 def OrIntL(self, up,formstring):
    if up > len(self.proof)-1:
      print("Range exceeded.")
      return
    newf = Formula(formstring)
    if newf == None:
     print("Syntax Error.")
     return 
     
    formu = Formula("(A v B)")
    
    formu.children = [newf, self.proof[up].formula]
    formu.left =  newf
    formu.right = self.proof[up].formula
   # aux = astop.NegationExpand(Formula("(" + formstring + " v " + parser.Printout(self.proof[up].formula)  +")"  ))
    proofelement = ProofElement("OrIntL",[up],[],[], astop.NegationExpand(formu))
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("OrIntL(" + str(up) + "," + '"'+ formstring + '"' + ")")
    
    return True
        

 def OrElim(self, up, left, c1, right, c2):
     
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return     
  if left > len(self.proof)-1:
    print("Range exceeded.")
    return
  if c1 > len(self.proof)-1:
    print("Range exceeded.")
    return
  if right > len(self.proof)-1:
    print("Range exceeded.")
    return
  if c2 > len(self.proof)-1:
    print("Range exceeded.")
    return              
     
  if left > c1 or right > c2:
    print("Subconclusion occurs before subhypothesis.")  
    return 
  if not self.proof[left].name =="Hyp" or not self.proof[right].name =="Hyp":
    print("Cannot discharge formula which is not an hypothesis.") 
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
  else:
    print("Rule not applicable")
    
        
 def ForallElim (self, up,termstring):
   term1 = Term(termstring)     
   if term1 == None:
    print("Syntax Error.")
    return     
     
   if up > len(self.proof)-1:
     print("Range exceeded.")
     return
     
   if self.proof[up].formula.operator.name=="forall":
    form = copy.deepcopy(self.proof[up].formula)   
    term = astop.NegationExpand(term1)
    proofelement = ProofElement("ForallElim", [up],[term],[], astop.Substitution( astop.Free(form.children[0],[]) , form.operator.variable, term) )
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("ForallElim(" + str(up) +"," + '"' + termstring +'"' +")")
    
    return True

 def ExistsInst (self, up, newvar):
     
   if up > len(self.proof)-1:
     print("Range exceeded.")
     return
   term = Term(newvar)
   if term== None:
    print("Syntax Error.")
    return             
     
   if self.proof[up].formula.operator.name=="exists":
    form = copy.deepcopy(self.proof[up].formula)   
  
    proofelement = ProofElement("Hyp", [],[],[], astop.Substitution( astop.Free(form.children[0],[]) , form.operator.variable, term) )
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("ExistsInst(" + str(up) +"," + '"' + newvar +'"' + ")")
    
    return True         

 def ForallInt (self, up, variablestring, quantvarstring):
     if up > len(self.proof)-1:
       print("Range exceeded.")
       return
     if quantvarstring in parser.constants:
        print("Cannot quantify over constant.")
        return None
     if not quantvarstring in parser.variables or not variablestring in parser.variables :
         print("Undefined symbol.")
         return None
     variable = parser.Term(tokenizer.Tokenize(variablestring))
     quantvar = parser.Term(tokenizer.Tokenize(quantvarstring))
     check = astop.GetFreeVars(astop.Free(self.proof[up].formula,[]),"Term")
     if quantvar.name in check:
       if quantvar.name != variablestring:
        print("Cannot rename bound variable to name of a free variable.")    
        return None
     for h in self.GetHypDep(self.proof[up]):
      if variable.name in [x for x in astop.GetFreeVars(astop.Free(self.proof[h].formula,[]),"Term")]:
       print("Variable to be quantified occurs free in a depending hypothesis.")            
       return None
     form = copy.deepcopy(self.proof[up].formula) 
     aux1 = astop.Substitution(form, variable, quantvar)
     #parser.Printout(aux1)
     formu = Formula("forall x. (x = x)")
     formu.operator.variable = quantvar
     formu.children = [aux1]
     
#     aux2 = parser.Formula(tokenizer.Tokenize("forall "+quantvar.name +"."+ parser.Printout(aux1) ))
     proofelement = ProofElement("ForallInt", [up],[variable,quantvar],[], formu) 
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("ForallInt(" + str(up) + "," + '"' + variablestring +'"' +"," + '"' + quantvarstring +'"' + ")")
     
     return True
     
     


 def ExistsElim(self,exists, sub, concl, inststring):
       
  if not self.proof[exists].formula.operator.name=="exists":
   print("Not an existential formula.")     
   return None
  inst = Term(inststring) 
  a = copy.deepcopy(self.proof[exists].formula)
  body = astop.Free(a.children[0],[])
  var = astop.Free(a.operator.variable,[])
  if not astop.Equals(astop.Substitution(body,var,inst),self.proof[sub].formula):
   print("Rule not applicable")        
   return None
  dep = [x for x in self.GetHypDep(self.proof[concl]) if x!= sub]
 
  for h in dep:
   aux = astop.GetFreeVars(astop.Free(self.proof[h].formula,[]),"Term")
   n = inst.name
   if n in aux:
    print("Variable occurs free in forbidden hypothesis.")  
    return None
  aux2 = astop.GetFreeVars(astop.Free(self.proof[exists].formula,[]),"Term"),
  if inst.name in aux2:
     print("Variable free in existential hypothesis.")
     return None
  aux3 = astop.GetFreeVars(astop.Free(copy.deepcopy(self.proof[concl].formula),[]),"Term")
  if inst.name in aux3:
     print("Variable free in conclusion.")
     return None         
  proofelement = ProofElement("ExistsElim", [exists,sub,concl],[inst],[], self.proof[concl].formula)
  proofelement.pos = len(self.proof) +1
  self.proof[sub].dischargedby.append(proofelement.pos)
  self.proof.append(proofelement)
  self.log.append("ExistsElim(" + str(exists) + "," + str(sub) +"," + str(concl) + "," + '"' + inststring +'"' + ")")
  
  return True

 def ExistsInt(self,up,termstring,newvarname,places):
    
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return     
  term = Term(termstring)     
  if term == None:
    print("Syntax Error.")
    return  
      
  if newvarname in parser.constants:
    print("Variable is a constant.")   
    return None    
  if not newvarname in parser.variables:
    print("Syntax Error.")
    return None     
  newvar = Term(newvarname)     
       
  aux = copy.deepcopy(self.proof[up].formula)
  form = astop.SubstitutionByPosition(aux, term, newvar, places)
  
  formu = Formula("exists x. (x = x)")
  formu.operator.variable = newvar
  formu.children = [form]
  
#  aux2 = parser.Printout(form)
#  out = parser.Formula(tokenizer.Tokenize("exists " + newvar.name +"." + aux2))
  proofelement = ProofElement("ExistsInt", [up],[termstring,newvarname,places],[], formu)
  proofelement.pos = len(self.proof) +1
  self.proof.append(proofelement)
  self.log.append("ExistsInt(" + str(up) + "," + '"' + termstring + '"'+ "," + '"' + newvarname + '"' + "," + PrintNumList(places) +")")
  
  return True


 def AbsI(self,up,formstring):
     
    if up > len(self.proof)-1:
      print("Range exceeded.")
      return 
      
    if parser.Printout(self.proof[up].formula) =="_|_":
     proofelement = ProofElement("AbsI", [up],[formstring],[], astop.NegationExpand(Formula(formstring)))
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
    
  if up > len(self.proof)-1:
    print("Range exceeded.")
    return     
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
  else:
   print("Not an equality.")
 
 def Identity (self, termstring):
      formu = parser.Formula(tokenizer.Tokenize("( x = x )"))
      ter = parser.Term(tokenizer.Tokenize(termstring))
      if ter==None:
        return None
      ter2 = copy.deepcopy(ter)    
      formu.children = [ter,ter2]
      formu.left = ter
      formu.right = ter2
      
      #aux = parser.Formula(tokenizer.Tokenize("("+termstring +" = " + termstring + ")") )
      #if aux==None:
       # print("Syntax Error.")  
        #return None
      proofelement= ProofElement("Identity", [],[termstring], [],formu)
      proofelement.pos = len(self.proof) + 1
      self.proof.append(proofelement)
      self.log.append("Identity(" + '"' + termstring +'"' + ")")
     
      return True

 def EqualitySub(self, up, eq , places):
     if up > len(self.proof)-1:
       print("Range exceeded.")
       return
     if eq > len(self.proof)-1:
       print("Range exceeded.")
       return  
     form = astop.Free(copy.deepcopy(self.proof[up].formula),[])
     equa = astop.Free(copy.deepcopy(self.proof[eq].formula),[])
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
    print(str(n)+". "+parser.PrettyPrintout(p.formula) +"  "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]) + " Qed" )
   else:
    print(str(n)+". "+parser.PrettyPrintout(p.formula) +"  "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]))      
   n = n + 1
   
 def ShowLog(self):
  n = 0        
  for l in self.log:
    print(str(n) + ". " + l)
    n = n + 1 
  print("")         
           
 def ShowLast(self):
   n = len(self.proof)-1
   if self.proof[n].qed:
    print(str(n)+". "+parser.PrettyPrintout(self.proof[n].formula) +" "+self.proof[n].name +" "+ ' '.join([str(y) for y in self.proof[n].dependencies]) + " Qed")         
   else:
    print(str(n)+". "+parser.PrettyPrintout(self.proof[n].formula) +" "+self.proof[n].name +" "+ ' '.join([str(y) for y in self.proof[n].dependencies]))
    
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
   if up > len(self.proof)-1:
     print("Range exceeded.")
     return     
   strargs2 = copy.deepcopy(strargs) 
   if not conceptname in self.definitions.keys():
    print("Predicate undefined.")
    return
   params = copy.deepcopy(self.definitions[conceptname]["arguments"])
   formul = copy.deepcopy(self.definitions[conceptname]["formula"])
   
   newparams = []
   for x in params:
     fresh = tokenizer.Fresh(parser.variables, tokenizer.alphabet)
     parser.variables.append(fresh)
     newparams.append(fresh)
     formul = copy.deepcopy(astop.Substitution( astop.Free(formul,[]) , Term(x), Term(fresh)))         
       
       
   args = [parser.Term(tokenizer.Tokenize(x)) for x in strargs2]     
   ast = copy.deepcopy(self.proof[up].formula)
   defs = copy.deepcopy(self.definitions)
   defs[conceptname]["formula"] = formul
   defs[conceptname]["arguments"] = newparams
  
   aux = astop.ConceptSub(ast,conceptname,args,positions,defs)
   proofelement = ProofElement("DefSub" , [up],[conceptname,args,positions], [],aux)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("DefSub(" + str(up) + "," + '"' +conceptname +'"' +  "," + PrintStrList(strargs) + "," + PrintNumList(positions) + ")")
  
   return True
   
 def DefExp(self,up,conceptname,positions):
   if up > len(self.proof)-1:
     print("Range exceeded.")
     return
   if not conceptname in self.definitions.keys():
    print("Predicate undefined.")
    return     
   ast = copy.deepcopy(self.proof[up].formula)
   ast = astop.PredicatePosition(ast,conceptname,0)[0]
   aux = astop.ConceptExp(ast,conceptname,positions,self.definitions)
   proofelement = ProofElement("DefExp" , [up],[conceptname,positions], [],aux)
   proofelement.pos = len(self.proof) + 1
   self.proof.append(proofelement)
   self.log.append("DefExp(" + str(up) + "," + '"' +conceptname + '"' + "," + PrintNumList(positions) +")")
   
   return True
    
 def NewDef(self, predname,args,formstring):
  if parser.Formula(tokenizer.Tokenize(formstring))== None:
   print("Syntax Error.")
   return    
  self.AddPredicate(predname,len(args),True) 
  self.AddVariables(args)    
  form = astop.NegationExpand(Formula(formstring))  
  self.definitions[predname]={"formula":form, "arguments":args}
  #self.log.append("NewDef(" + '"' +  predname+'"' + "," + PrintStrList(args) + "," + '"' + formstring+'"' + ")")
  
  return True 
 
 def NewDefEq(self,equationstring):
  
       
  equationstring = "("+equationstring +")"     
  if type(Formula(equationstring)).__name__!="Constructor":
     return None
  if Formula(equationstring).operator.name!="=":
      return None
  
  self.definitionequations.append(astop.NegationExpand(Formula(equationstring)))            
 # self.log.append("NewDefEq(" + '"' + equationstring + '"' + ")")
  
  return True
 
 #Also DelDef, DelAx, DelTheorem, Del EqDef

 def PredSub(self,up,predicatename,arguments,formstring,positions):
  form1 = Formula(formstring)
  if form1==None:
   print("Syntax Error.")
   return      
  if predicatename in self.definitions.keys():
    print("Predicate is defined.")
    return None
  ast = copy.deepcopy(self.proof[up].formula)
  ast = astop.PredicatePosition(ast,predicatename,0)[0]
  auxdef={}    
  auxdef[predicatename] ={ "arguments":arguments, "formula":astop.NegationExpand(form1)}
  aux = astop.ConceptExp(ast,predicatename,positions,auxdef)
  proofelement = ProofElement("PredSub" , [up],[predicatename,arguments,formstring,positions], [],aux)
  proofelement.pos = len(self.proof) + 1
  self.proof.append(proofelement)
  self.log.append("PredSub(" + str(up) + "," + '"'+ predicatename +'"' +"," + PrintStrList(arguments) +"," + '"'+ formstring+'"' + "," + PrintNumList(positions) + ")")
  
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
     myvar = astop.Free(aux.operator.variable,[])
     bod = astop.Free(aux.children[0],[])
     bod2 = parser.Printout(astop.Substitution(copy.deepcopy(bod), myvar, Term(newbound)))
     exis = Formula("exists " + myvar.name +"." + "(" + parser.Printout(bod) + " & " + "forall "+ newbound + ". (" + bod2  + " -> (" + newbound + " = " +myvar.name +") ) )")
     proofelement = ProofElement("UniqueElim" , [up],[], [],exis)
     proofelement.pos = len(self.proof) + 1
     self.log.append("UniqueElim(" + str(up)+ "," + '"' + newbound + '"' + ")")
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
                         self.log.append("UniqueInt(" + str(up)+")")
                         
                         return True  
                  
 def ClassElim(self,up):
  if self.proof[up].formula.name=="constructor":
    if self.proof[up].formula.operator.name=="Elem":    
      #if type(self.proof[up].formula.left).__name__=="Leaf":
        myvar = astop.Free(copy.deepcopy(self.proof[up].formula.left) ,[]) 
        if self.proof[up].formula.right.name == "constructor":
         if self.proof[up].formula.right.operator.name =="extension":
            body = astop.Free(copy.deepcopy(self.proof[up].formula.right.children[0]),[])
            boundvar = astop.Free(copy.deepcopy(self.proof[up].formula.right.operator.variable),[])  
            
            newbod = astop.Substitution(body,boundvar,myvar)
            setfor = Formula(" Set(" + parser.Printout(myvar) +")" )
            formu = Formula("(A & A)")
            formu.children = [setfor,newbod]
            formu.left = setfor
            formu.right = newbod 
            
                     
        #    aux = Formula("( Set(" + parser.Printout(myvar) +") & "+ parser.Printout(astop.Substitution(body,boundvar,myvar)) + ")" )     
            proofelement = ProofElement("ClassElim" , [up],[], [],formu)
            proofelement.pos = len(self.proof) + 1
            self.proof.append(proofelement)
            self.log.append("ClassElim(" + str(up) + ")")
            
            return True
   
 def ClassInt(self,up,newvarname):
  form = copy.deepcopy(self.proof[up].formula)  
  newvar = astop.Free(Term(newvarname),[])   
  if form.name =="constructor":
      if form.operator.name=="&":
        if form.left.name=="constructor": 
         if form.left.operator.name=="Set":
           if form.left.children[0].name!="constructor":
             var = form.left.children[0]
             body = form.right
             newbod = astop.Substitution(body,var,newvar )
             exten = Term("extension x. (x = x)")
             exten.operator.variable = Term(newvarname) 
             exten.children = [newbod]
             formu = Formula("Elem(x,x)")
             formu.children = [var, exten]
             formu.left = var
             formu.right = exten
             
             #aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("ClassInt" , [up],[newvarname], [],formu)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("ClassInt(" + str(up) + "," + '"' +newvarname +'"' + ")")
            
             return True            
   
        if form.right.name=="constructor": 
         if form.right.operator.name=="Set":
           if form.right.children[0].name!="constructor":
             var = form.right.children[0]
             body = form.left
             
             newbod = astop.Substitution(body,var,newvar )
             exten = Term("extension x. (x = x)")
             exten.operator.variable = Term(newvarname) 
             exten.children = [newbod]
             formu = Formula("Elem(x,x)")
             formu.children = [var, exten]
             formu.left = var
             formu.right = exten
             
             
             #aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("ClassInt" , [up],[newvarname], [],formu)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("ClassInt(" + str(up) + "," + '"' + newvarname + '"' + ")")
             
             return True            
        
 
 #for Second-Order Arithmetic
 
 def SetElim(self,up):
  if self.proof[up].formula.name=="constructor":
    if self.proof[up].formula.operator.name=="Elem":    
      #if type(self.proof[up].formula.left).__name__=="Leaf":
        myvar = astop.Free(copy.deepcopy(self.proof[up].formula.left) ,[]) 
        if self.proof[up].formula.right.name == "constructor":
         if self.proof[up].formula.right.operator.name =="extension":
            body = astop.Free(copy.deepcopy(self.proof[up].formula.right.children[0]),[])
            boundvar = astop.Free(copy.deepcopy(self.proof[up].formula.right.operator.variable),[])  
            
            newbod = astop.Substitution(body,boundvar,myvar)
            setfor = Formula(" Nat(" + parser.Printout(myvar) +")" )
            formu = Formula("(A & A)")
            formu.children = [setfor,newbod]
            formu.left = setfor
            formu.right = newbod 
            
                     
        #    aux = Formula("( Set(" + parser.Printout(myvar) +") & "+ parser.Printout(astop.Substitution(body,boundvar,myvar)) + ")" )     
            proofelement = ProofElement("SetElim" , [up],[], [],formu)
            proofelement.pos = len(self.proof) + 1
            self.proof.append(proofelement)
            self.log.append("SetElim(" + str(up) + ")")
            
            return True
   
 def SetInt(self,up,newvarname):
  form = copy.deepcopy(self.proof[up].formula)  
  newvar = astop.Free(Term(newvarname),[])   
  if form.name =="constructor":
      if form.operator.name=="&":
        if form.left.name=="constructor": 
         if form.left.operator.name=="Nat":
           if form.left.children[0].name!="constructor":
             var = form.left.children[0]
             body = form.right
             newbod = astop.Substitution(body,var,newvar )
             exten = Term("extension x. (x = x)")
             exten.operator.variable = Term(newvarname) 
             exten.children = [newbod]
             formu = Formula("Elem(x,x)")
             formu.children = [var, exten]
             formu.left = var
             formu.right = exten
             
             #aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("SetInt" , [up],[newvarname], [],formu)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("SetInt(" + str(up) + "," + '"' +newvarname +'"' + ")")
            
             return True            
   
        if form.right.name=="constructor": 
         if form.right.operator.name=="Nat":
           if form.right.children[0].name!="constructor":
             var = form.right.children[0]
             body = form.left
             
             newbod = astop.Substitution(body,var,newvar )
             exten = Term("extension x. (x = x)")
             exten.operator.variable = Term(newvarname) 
             exten.children = [newbod]
             formu = Formula("Elem(x,x)")
             formu.children = [var, exten]
             formu.left = var
             formu.right = exten
             
             
             #aux = Formula("Elem(" +var.name + ", extension " + newvarname  + " . "  + parser.Printout( astop.Substitution(body,var,newvar ) ) +")" )
             proofelement = ProofElement("SetInt" , [up],[newvarname], [],formu)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("SetInt(" + str(up) + "," + '"' + newvarname + '"' + ")")
             
             return True            
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
 def PolySub(self,up,polyvarname,formstring):
     if up > len(self.proof)-1:
       print("Range exceeded.")
       return
     
     
     
     for h in self.GetHypDep(self.proof[up]):
      if polyvarname in astop.GetPolyVars(self.proof[h].formula):
       return None            
     form = copy.deepcopy(self.proof[up].formula)
     aux = astop.Substitution(form, Formula(polyvarname),astop.NegationExpand(Formula(formstring))) 
     proofelement = ProofElement("PolySub" , [up],[polyvarname,formstring], [],aux)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("PolySub(" + str(up) + "," + '"' + polyvarname + '"' + "," + '"' + formstring +'"'+ ")")
     
     return True   
 
      
 def LoadTheorem(self,name):
  global Proof    
  f = open(name,'rb')
  data = pickle.load(f)
  theorem = data["proofenv"].proof[-1].formula
  self.theorems.append(theorem)
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
   dire.sort()
   os.chdir(name)
   for t in dire:
    if t[0]!= '.':   
     print(self.ViewTheorem(t))
   os.chdir("..")     
   return True    
  
  
#shortcuts
  
 def FreeSub(self,up, freevar,instance):
  self.ForallInt(up,freevar,freevar)
  self.ForallElim(len(self.proof)-1,instance) 
  return True     
 
 def EquivJoin(self,left,right):
   self.AndInt(left,right)
   self.EquivConst(len(self.proof)-1)
   return True
   
 def EquivLeft(self,up):
   self.EquivExp(up)
   self.AndElimL(len(Proof.proof)-1)  
   return True
  
 def EquivRight(self,up):
   self.EquivExp(up)
   self.AndElimR(len(Proof.proof)-1)  
   return True 
   
   
 def Undo(self):
        
   n = len(Proof.proof)
   self.proof.pop()
   for p in Proof.proof:
     if n in p.dischargedby:  
      p.dischargedby.remove(n)
   self.log.pop()  
       
   return True
 
 def UsedTheorems(self):
    used = [] 
    for l in self.log:
     if l[0:10]=="TheoremInt":
      x = int(l[11:len(l)-1])
      if not x in used:
       used.append(x)
      
       print(str(x) + ". " + parser.PrettyPrintout(self.theorems[x]))     
    return True
  
  
       
def GenerateProof():
  for v in parser.variables:
   if '_' in v:
    parser.variables.remove(v)    
  Proof.proof = [] 
  aux = Proof.log
  Proof.log = []        
  for logelem in aux:
     
         
  
     exec("Proof." + logelem)
  
  if len(Proof.proof)>0: 
   last = len(Proof.proof)-1
   Proof.Qed(last) 
   ShowProof() 
   
            
         
      
      
      
      
      
      
      
      
                        
           
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
 if Proof.Hyp(form):   
 
  ShowProof()
  return True
          
def NewAx(formstring):
  if Proof.NewAx(formstring) :
  
     ShowAxioms()
     return True    
     
def AxInt(axnum):
    if Proof.AxInt(axnum): 
    
     ShowProof()
     return True
     
def EquivExp(up):
 if Proof.EquivExp(up):
     ShowProof()
     return True
     
def EquivConst(up):
    if Proof.EquivConst(up):
        ShowProof()
        return True
        
def DefEqInt(axnum):
      if Proof.DefEqInt(axnum) :
          ShowProof()
          return True
          
def AddTheorem(formstring):
    if Proof.AddTheorem(formstring):
        ShowTheorems()
        return True
             
def TheoremInt(axnum):
    if Proof.TheoremInt(axnum):
     ShowProof()
     return True
              
def Qed(up):
     if Proof.Qed(up):
      ShowProof()
      return True
       
def AndInt(left,right):
    if Proof.AndInt(left,right):
     ShowProof()
     return True
     
def AndElimL(up):
    if Proof.AndElimL(up):
     ShowProof()
     return True
     
def AndElimR (up):
    if Proof.AndElimR (up):
     ShowProof()
     return True
     
def ImpElim (left,right):
    if Proof.ImpElim(left,right):
     ShowProof()
     return True
     
def ImpInt(up,dis):
    if Proof.ImpInt(up,dis):
        ShowProof()
        return True
        
def OrIntR(up,formstring):
    if Proof.OrIntR(up,formstring):
        ShowProof()
        return True
        
def OrIntL(up,formstring):
    if Proof.OrIntL(up,formstring):
        ShowProof()
        return True
        
def OrElim(up, left, c1, right, c2):
    if Proof.OrElim(up, left, c1, right, c2):
        ShowProof()
        return True
        
def ForallElim(up,termstring):
    if Proof.ForallElim (up,termstring):
        ShowProof()
        return True
        
def ForallInt(up, variablestring, quantvarstring):
    if Proof.ForallInt(up, variablestring, quantvarstring):
        ShowProof()
        return True
def ExistsElim(exists, sub, concl, inststring):
    if Proof.ExistsElim(exists, sub, concl, inststring):
      ShowProof()
      return True
def ExistsInt(up,termstring,newvarname,places):
    if Proof.ExistsInt(up,termstring,newvarname,places):
     ShowProof()
     return True
     
def AbsI(up,formstring):
    if Proof.AbsI(up,formstring):
     ShowProof()
     return True
     
def AbsC(abs,neghyp):
    if Proof.AbsC(abs,neghyp):
        ShowProof()
        return True
def Symmetry(up):
    if Proof.Symmetry( up):
        ShowProof()
        return True
        
def Identity ( termstring):
    if Proof.Identity ( termstring):
        ShowProof()
        return True
        
def EqualitySub(up, eq , places):
    if Proof.EqualitySub(up, eq , places):
        ShowProof()
        return True
        
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
    if Proof.DefSub(up,conceptname,strargs,positions):
        ShowProof()
        return True
def DefExp(up,conceptname,positions):
    if Proof.DefExp(up,conceptname,positions):
      ShowProof()
      return True
def NewDef( predname,args,formstring):
    if Proof.NewDef( predname,args,formstring):
     ShowDefinitions()
     return True
     
     
def NewDefEq(equationstring):
    if Proof.NewDefEq(equationstring):
        ShowDefEquations()
        return True
        
def PredSub(up,predicatename,arguments,formstring,positions):
    if Proof.PredSub(up,predicatename,arguments,formstring,positions):
        ShowProof()
        return True
        
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
    if Proof.ClassElim(up):
        ShowProof()
        return True
def ClassInt(up,newvarname):
    if Proof.ClassInt(up,newvarname):
        ShowProof()
        return True
def PolySub(up,polyvarname,formstring):
    if Proof.PolySub(up,polyvarname,formstring):
        ShowProof()
        return True
def LoadTheorem(name):
    if Proof.LoadTheorem(name):
     print(str(len(Proof.theorems)-1) + ". " + parser.PrettyPrintout(Proof.theorems[len(Proof.theorems) -1]))
     return True
def FreeSub(up,freevar,instance):
    if Proof.FreeSub(up,freevar,instance):
        ShowProof()
        return True
        
def ViewTheorem(name):
    return Proof.ViewTheorem(name) 
          
def Undo():
    Proof.log.pop()
    for v in parser.variables:
     if '_' in v:
      parser.variables.remove(v)
    GenerateProof()
    return True
             
def EquivJoin(left,right):
    if Proof.EquivJoin(left,right):
        ShowProof()
        return True
        
def EquivLeft(up):
    if Proof.EquivLeft(up):
        ShowProof()
        return True
        
def EquivRight(up):
    if Proof.EquivRight(up):
        ShowProof()
        return True
        
def UniqueElim(up,newbound):    
    if Proof.UniqueElim(up,newbound):
        ShowProof()
        return True
        
def UniqueInt(up):    
    if Proof.UniqueInt(up) :
        ShowProof()
        return True
          
def ViewTheory(name):     
    return Proof.ViewTheory(name)
    
def ExistsInst (up, newvar):  
    if Proof.ExistsInst(up,newvar):
        ShowProof()
        return True  
    
def UsedTheorems():
 Proof.UsedTheorems()
 return True
 
def Hypotheses(n):
  if n < len(Proof.proof):
    return set(Proof.GetHypDep(copy.deepcopy(Proof.proof[n])))    
    
def preMultiFreeSub(up,sourcelist,targetlist):
  global Proof    
  if len(sourcelist)!=len(targetlist):
    return None
  if len(sourcelist) ==1:
    return Proof.FreeSub(up,sourcelist[0],targetlist[0])    
  
  Proof.FreeSub(up, sourcelist[0],targetlist[0])
  return preMultiFreeSub(up+1, sourcelist[1:], targetlist[1:])           

def MultiFreeSub(up,sourcelist,targetlist):
  if preMultiFreeSub(up,sourcelist,targetlist):
       ShowProof()
       return True 
       
def PredSub(up,predicatename,arguments,formstring,positions):
    if Proof.PredSub(up,predicatename,arguments,formstring,positions): 
        ShowProof()
        return True      
        
        
def CheckTheory(namelist):
  start = time.time()
  global Proof    
  tot = 0
  pret = parser.pretty
  for x in namelist:
     print("")
     Load(x)
#     parser.pretty = copy.deepcopy(pret)
     old = parser.variables
     th = parser.PrettyPrintout(Proof.proof[len(Proof.proof)-1].formula)
     print(x + ". " + th)
     print("")
     GenerateProof()
     print("")
     print("Used Theorems")
     print("")
     UsedTheorems()
     
     tot = tot + len(Proof.proof)
  print("")
  finish = time.time()-start
  print("Succesfully checked " + str(len(namelist)) + " theorems with a total of " +str(tot) + " lines in " + str(int(finish)) + " seconds.")
  Load("Default")

def CheckTheoryLog(namelist):
 global Proof    
 tot = 0
 for x in namelist:
    print("")
    Load(x)
    th = parser.PrettyPrintout(Proof.proof[len(Proof.proof)-1].formula)
    print(x + ". " + th)
    print("")
    ShowLog()
    print("")
      
   
 print("")
 Load("Default")


def ParseLog():
 aux = []    
 global Proof
 for l in Proof.log:
  for c in range(0,len(l)):
    if l[c]=="(":
     aux.append( [l[0:c]] + l[c+1:len(l)-1].split(',') )
     break
 return aux     
     
def LogToString(log):
 aux = []
 for l in log:
  aux.append( l[0] + "(" + (',').join( l[1:]) +")")
 return aux          
     
def ProofEdit(init,offset):
 global Proof    
 aux = []    
 auxlog = ParseLog()
 for l in auxlog:
  if l[0] in ["AbsI", "ExistsInt", "DefSub", "DefExp","ExistsInst", "ForallInt","ForallElim", "ClassElim", "AndElimL","AndElimR", "ClassInt","EquivExp", "Symmetry","PolySub","OrIntL","OrIntR","EquivConst"]:
    if int(l[1])>init-1:
      l[1] = str(int(l[1]) + offset)
    aux.append(l)
    continue
  if l[0] in ["ImpElim", "ImpInt", "AndInt" , "EqualitySub"]:
     if int(l[1])>init-1:
       l[1] = str(int(l[1]) + offset)
     if int(l[2])>init-1:
       l[2] = str(int(l[2]) + offset)           
     aux.append(l)       
     continue
  if l[0] in ["ExistsElim", "AbsC"]:
     if int(l[1])>init-1:
       l[1] = str(int(l[1]) + offset)
     if int(l[2])>init-1:
       l[2] = str(int(l[2]) + offset)
     if int(l[3])>init-1:
       l[3] = str(int(l[3]) + offset)  
     aux.append(l)       
     continue
  
       
  if l[0] =="OrElim":
     if int(l[1])>init-1:
       l[1] = str(int(l[1]) + offset)
     if int(l[2])>init-1:
       l[2] = str(int(l[2]) + offset) 
     if int(l[3])>init-1:
        l[3] = str(int(l[3]) + offset)
     if int(l[4])>init-1:
        l[4] = str(int(l[4]) + offset)                  
     if int(l[5])>init-1:
         l[5] = str(int(l[5]) + offset)
     aux.append(l)
     continue
  aux.append(l)      
  
 pad = []
 for n in range(0,offset):
  pad.append(['Identity','"x"' ])     
 aux1 = aux[:init] + pad + aux[init:] 
 Proof.log = LogToString(aux1)
 ShowLog()
 return True
 
def Test():
 CheckTheory(["Th4","Th5","Th6","Th7","Th8",
 "Th11","Th12", "Th14","Th16","Th17","Th19","Th20","Th21", 
 "Th24","Th26","Th27","Th28","Th29","Th30",
 "Th31","Th32","Th33", "Th34","Th35", "Th37","Th38",
 "Th39","Th41", "Th42","Th43","Th44" ,   "Th46","Th47","Th49","Th50","Th53","Th54","Th55", "Th58", "Th59", "Th61", "Th62",  "Th64", "Th67", "Th69", "Th70", "Th71" , "Th73" ,"Th74","Th75", "Th77", "Th88", "Th90","Th91","Th92","FunctionApp","Th94","1-to-1","FunctionRange","Th96", "FunctionApp2","FunctionInvApp", "FunctionDomRange","FunctionPair","Th97","PairEquals","WellOrdersSubset","ContCompl","Th99", "Th100aux","Th100"])

# CheckTheoryLog(["Th4","Th5","Th6","Th7","Th8",
# "Th11","Th12", "Th14","Th16","Th17","Th19","Th20","Th21", 
# "Th24","Th26","Th27","Th28","Th29","Th30",
# "Th31","Th32","Th33", "Th34","Th35", "Th37","Th38",
# "Th39","Th41", "Th42","Th43","Th44" ,   "Th46","Th47","Th49","Th50","Th53","Th54","Th55", "Th58", "Th59", "Th61", "Th62",  "Th64", "Th67", "Th69", "Th70", "Th71" , "Th73" , "Th74","Th75", "Th77", "Th88", "Th90"])
 

def Fresh(up):
 global Proof
 formula = astop.Free(copy.deepcopy(Proof.proof[up].formula)  ,[])
 variables = list(set(astop.GetFreeVars(formula,"Term")))
 newvariables= []
 
 for x in variables:
            
   fresh = tokenizer.Fresh(parser.variables, tokenizer.alphabet)
   parser.variables.append(fresh)
   newvariables.append(fresh)
     
 
 start = True
 for n in range(0,len(variables)):
              
   if start ==True:
    if not Proof.FreeSub(up, variables[n],newvariables[n]):
     continue
    else:
      start = False 
      continue      
   if start ==False:
    Proof.FreeSub(len(Proof.proof)-1, variables[n],newvariables[n])  
 
 ShowProof()  
 return True  
 

def ViewInput(up):
  global Proof    
  if up > len(Proof.proof)-1:
    print("Range exceeded.")
    return 
  print(parser.TruePrintout(Proof.proof[up].formula))
  return True
   
 
                       
         
            
