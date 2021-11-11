import parser
import tokenizer
import astop
import pickle
import copy
import os


def next(list):
 n = list[0]
 for m in list:
  if m > n:
    n = m
 return n+1  


def Inc(p,mem):
 for f in mem:
  if astop.Equals(p,f):
      return True
 return False        


def SeqEquals(a,b):
 if astop.Equals(a.head, b.head):
  for p in a.body:
    if not Inc(p,b.body):
     return False
  for q in b.body:
    if not Inc(q,a.body):
     return False
  return True     
 return False

def SeqInc(p,mem):
 for f in mem:
  if SeqEquals(p,f):
      return True
 return False              


class Sequent:
 def __init__(self, head,body):
    self.head = head
    self.body = body
    self.id = 0
    self.parent = 0
    self.rule = ""
 def display(self):
  aux = ""
  for s in self.body:
    aux = aux + ", "+ parser.PrettyPrintout(s)
  head = parser.PrettyPrintout(self.head)
  return aux[1:] + " => " + head             

class SequentList:
 def __init__(self,formstring):
   form = astop.NegationExpand(parser.Formula(tokenizer.Tokenize(formstring)))
   seq = Sequent(form,[])
   self.sequentlist = [seq]
   self.memory = []
   self.proof = []
   self.used = [0]
   self.collection = []

 def display(self):
   if len(self.sequentlist) == 0:
     print("<empty>")     
   n = 0     
   for  p in self.sequentlist:
    print(str(n)+". "+ p.display())    
    n = n + 1     



   
def rand(seq,n):
   if  n < len(seq.sequentlist)  and seq.sequentlist[n].head.name=="constructor":
      if seq.sequentlist[n].head.operator.name=="&":
         aux1 = seq.sequentlist[:n]
         aux2 = seq.sequentlist[n+1:]
         aux3 = seq.sequentlist[n].body
         left = seq.sequentlist[n].head.left
         right = seq.sequentlist[n].head.right
         new1 = Sequent(left,aux3)
         new2 = Sequent(right, aux3)
         if not SeqInc(new1, seq.memory) and not SeqInc(new2,seq.memory):
          seq.sequentlist = aux1 + [new1,new2] + aux2
          seq.memory.append(new1)
          seq.memory.append(new2)
          seq.proof.append(["u",0,n])
          return seq
   return False
   
def ror1(seq,n):
    if  n < len(seq.sequentlist)  and seq.sequentlist[n].head.name=="constructor":
       if seq.sequentlist[n].head.operator.name=="v":
          aux1 = seq.sequentlist[:n]
          aux2 = seq.sequentlist[n+1:]
          aux3 = seq.sequentlist[n].body
          left = seq.sequentlist[n].head.left
          new1 = Sequent(left,aux3)
          if not SeqInc(new1,seq.memory):
    
           seq.sequentlist = aux1 + [new1] + aux2
           seq.memory.append(new1)
           seq.proof.append(["u",1,n])
           return seq
    return False             
    
def ror2(seq,n):
    if  n < len(seq.sequentlist)  and seq.sequentlist[n].head.name=="constructor":
       if seq.sequentlist[n].head.operator.name=="v":
          aux1 = seq.sequentlist[:n]
          aux2 = seq.sequentlist[n+1:]
          aux3 = seq.sequentlist[n].body
          right = seq.sequentlist[n].head.right
          new1 = Sequent(right,aux3)
          if not SeqInc(new1,seq.memory):
              
           seq.sequentlist = aux1 + [new1] + aux2
           seq.memory.append(new1)
           seq.proof.append(["u",2,n] )
           return seq
    return False
    
            
def rimp(seq,n):
     if  n < len(seq.sequentlist) and seq.sequentlist[n].head.name=="constructor":
        if seq.sequentlist[n].head.operator.name=="->":
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           aux3 = seq.sequentlist[n].body
           right = seq.sequentlist[n].head.right
           left = seq.sequentlist[n].head.left
           new1 = Sequent(right,[left] + aux3)
           if not SeqInc(new1,seq.memory):
            seq.sequentlist = aux1 + [new1] + aux2
            seq.memory.append(new1)
            seq.proof.append(["u",3,n])
            return seq
     return False  
     
def land(seq,n,m):
     if  n < len(seq.sequentlist):
      if m < len(seq.sequentlist[n].body):
       if seq.sequentlist[n].body[m].name == "constructor":            
        if seq.sequentlist[n].body[m].operator.name=="&":
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody = left + [a,b] + right
           new1 = Sequent(head,newbody)
           if not SeqInc(new1,seq.memory):
            seq.sequentlist = aux1 + [new1] + aux2
            seq.memory.append(new1)
            seq.proof.append(["b",0,n,m])
            return seq
     return False
     
def lor(seq,n,m):
     if  n < len(seq.sequentlist):
      if m < len(seq.sequentlist[n].body):
       if seq.sequentlist[n].body[m].name=="constructor" :           
        if seq.sequentlist[n].body[m].operator.name=="v":
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody1 = left + [a] + right
           newbody2 = left + [b] + right
           new1 = Sequent(head,newbody1)
           new2 = Sequent(head,newbody2)
           if not SeqInc(new1,seq.memory) and not SeqInc(new2, seq.memory):
            seq.sequentlist = aux1 + [new1,new2] + aux2
            seq.memory.append(new1)
            seq.memory.append(new2)
            seq.proof.append(["b",1,n,m])
            return seq
     return False                  
     
def limp(seq,n,m):
     if  n < len(seq.sequentlist):
      if m < len(seq.sequentlist[n].body):
       if seq.sequentlist[n].body[m].name=="constructor" :           
        if seq.sequentlist[n].body[m].operator.name=="->":
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody1 = seq.sequentlist[n].body
           newbody2 = left + [b] + right
           new1 = Sequent(a,newbody1)
           new2 = Sequent(head,newbody2)
           if not SeqInc(new1,seq.memory) and not SeqInc(new2, seq.memory):
            seq.sequentlist = aux1 + [new1,new2] + aux2
            seq.memory.append(new1)
            seq.memory.append(new2)
            seq.proof.append(["b",2,n,m])
            return seq
     return False     
     
def labs(seq,n,m):
     if  n < len(seq.sequentlist):
      if m < len(seq.sequentlist[n].body):
       if seq.sequentlist[n].body[m].name=="constructor" :           
        if seq.sequentlist[n].body[m].operator.name=="_|_":
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           seq.sequentlist = aux1 +  aux2
           seq.proof.append(["b",3,n,m])
           return seq
     return False   
     
def ax(seq,n,m):
     if  n < len(seq.sequentlist):
      if m < len(seq.sequentlist[n].body):
       if astop.Equals(seq.sequentlist[n].body[m], seq.sequentlist[n].head): 
           form = seq.sequentlist[n].display()        
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           seq.sequentlist = aux1 +  aux2
           seq.proof.append(["b",4,n,m,form])
           return seq
     return False      



def CodeApply(code,seq):
 aux = copy.deepcopy(seq)
 if code[0]=="u":
   if code[1] == 0:
     return rand(aux,code[2])     
   if code[1] == 1:
     return ror1(aux,code[2])  
   if code[1] == 2:
     return ror2(aux,code[2])
   if code[1] == 3:
     return rimp(aux,code[2])  
 if code[0] =="b":
   if code[1] == 0:
     return land(aux,code[2],code[3])     
   if code[1] == 1:
     return lor(aux,code[2],code[3])  
   if code[1] == 2:
     return limp(aux,code[2],code[3])
   if code[1] == 3:
     return labs(aux,code[2],code[3])
   if code[1] == 4:
     return ax(aux,code[2],code[3]) 
     

def RuleDisplay(code):
  
  if code[0]=="u":
    n =  code[2]   
    if code[1] == 0:
      return "rand(" + str(n) + ")"     
    if code[1] == 1:
      return "ror1("  + str(n) + ")"  
    if code[1] == 2:
      return "ror2(" + str(n) + ")" 
    if code[1] == 3:
      return "rimp(" + str(n) + ")" 
  if code[0] =="b":
    n = code[2]
    m = code[3]   
    if code[1] == 0:
      return "land(" + str(n) + "," + str(m) + ")"    
    if code[1] == 1:
      return "lor(" + str(n) + "," + str(m) + ")"  
    if code[1] == 2:
      return "imp(" + str(n) + "," + str(m) + ")"  
    if code[1] == 3:
      return "labs(" + str(n) + "," + str(m) + ")"  
    if code[1] == 4:
      return "ax(" + str(n) + "," + str(m) + ")  " + code[4]  
   
def RulesDisplay(proof):
 n = 1
 for p in proof:
  print(str(n) + ". " + RuleDisplay(p))    
  n = n+ 1

     
def search(seq):
          
   if len(seq.sequentlist)==0:
     return [True, seq.proof]
   for s in range(0,len(seq.sequentlist)):
       
  
     
    for f in range(0,len(seq.sequentlist[s].body)):
      
       for app in range(0,5):
      
        
        newseq = CodeApply(["b",app, s,f],seq)
        if not newseq==False:
             
         if search(newseq)[0]:
             return search(newseq)    
             
        
    for app in range(0,4):   
       
             
        newseq = CodeApply(["u",app,s], seq)
        if not newseq==False:
              
          if search(newseq)[0]:
              return search(newseq)
        
         
   return [False,["<no proof>"]]

State = {}
def Auto(formstring):
   global State
   State = SequentList(formstring)     


           
   
def Rand(seq,n):
   
         aux1 = seq.sequentlist[:n]
         aux2 = seq.sequentlist[n+1:]
         aux3 = seq.sequentlist[n].body
         left = seq.sequentlist[n].head.left
         right = seq.sequentlist[n].head.right
         new1 = Sequent(left,aux3)
         new2 = Sequent(right, aux3)
         new1.id = next(seq.used)
         new1.parent = seq.sequentlist[n].id
         seq.used.append(new1.id)
         new2.id = next(seq.used)
         new2.parent = seq.sequentlist[n].id
         seq.used.append(new2.id)
         
         seq.collection.append(seq.sequentlist[n])
         seq.sequentlist = aux1 + [new1,new2] + aux2
        
         return seq
   
   
def Ror1(seq,n):
    
          aux1 = seq.sequentlist[:n]
          aux2 = seq.sequentlist[n+1:]
          aux3 = seq.sequentlist[n].body
          left = seq.sequentlist[n].head.left
          new1 = Sequent(left,aux3)
          new1.id = next(seq.used)
          new1.parent = seq.sequentlist[n].id
          seq.used.append(new1.id)
          seq.collection.append(seq.sequentlist[n])
          seq.sequentlist = aux1 + [new1] + aux2
          
          return seq
               
    
def Ror2(seq,n):
   
          aux1 = seq.sequentlist[:n]
          aux2 = seq.sequentlist[n+1:]
          aux3 = seq.sequentlist[n].body
          right = seq.sequentlist[n].head.right
          new1 = Sequent(right,aux3)
          new1.id = next(seq.used)
          new1.parent = seq.sequentlist[n].id
          seq.used.append(new1.id)
          seq.collection.append(seq.sequentlist[n])   
          seq.sequentlist = aux1 + [new1] + aux2
          
          return seq
    
    
            
def Rimp(seq,n):
    
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           aux3 = seq.sequentlist[n].body
           right = seq.sequentlist[n].head.right
           left = seq.sequentlist[n].head.left
           new1 = Sequent(right,[left] + aux3)
           new1.id = next(seq.used)
           new1.parent = seq.sequentlist[n].id
           seq.used.append(new1.id)
           seq.collection.append(seq.sequentlist[n]) 
           seq.sequentlist = aux1 + [new1] + aux2
           
           return seq
     
     
def Land(seq,n,m):
    
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody = left + [a,b] + right
           new1 = Sequent(head,newbody)
           new1.id = next(seq.used)
           new1.parent = seq.sequentlist[n].id
           seq.used.append(new1.id)
           seq.collection.append(seq.sequentlist[n]) 
           seq.sequentlist = aux1 + [new1] + aux2
           
           return seq
     
     
def Lor(seq,n,m):
    
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody1 = left + [a] + right
           newbody2 = left + [b] + right
           new1 = Sequent(head,newbody1)
           new2 = Sequent(head,newbody2)
           
           new1.id = next(seq.used)
           new1.parent = seq.sequentlist[n].id
           seq.used.append(new1.id)
          
           new2.id = next(seq.used)
           new2.parent = seq.sequentlist[n].id
           seq.used.append(new2.id)
           seq.collection.append(seq.sequentlist[n])
           seq.sequentlist = aux1 + [new1,new2] + aux2
          
           return seq
                   
     
def Limp(seq,n,m):
    
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           head = seq.sequentlist[n].head
           left = seq.sequentlist[n].body[:m]
           right = seq.sequentlist[n].body[m+1:]
           a = seq.sequentlist[n].body[m].left
           b = seq.sequentlist[n].body[m].right
           newbody1 = seq.sequentlist[n].body
           newbody2 = left + [b] + right
           new1 = Sequent(a,newbody1)
           new2 = Sequent(head,newbody2)
           new1.id = next(seq.used)
           new1.parent = seq.sequentlist[n].id
           seq.used.append(new1.id)
           new2.id = next(seq.used)
           new2.parent = seq.sequentlist[n].id
           seq.used.append(new1.id)
           seq.collection.append(seq.sequentlist[n]) 
           seq.sequentlist = aux1 + [new1,new2] + aux2
           
           return seq
     
     
def Labs(seq,n,m):
    
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           
          
           seq.collection.append(seq.sequentlist[n])
           seq.sequentlist = aux1 +  aux2
           return seq
    
     
def Ax(seq,n,m):
    
           form = seq.sequentlist[n].display()        
           aux1 = seq.sequentlist[:n]
           aux2 = seq.sequentlist[n+1:]
           seq.collection.append(seq.sequentlist[n])
           seq.sequentlist = aux1 +  aux2
          
           return seq
         

def TreeCodeApply(code,seq):
 aux = copy.deepcopy(seq)
 if code[0]=="u":
   if code[1] == 0:
     return Rand(aux,code[2])     
   if code[1] == 1:
     return Ror1(aux,code[2])  
   if code[1] == 2:
     return Ror2(aux,code[2])
   if code[1] == 3:
     return Rimp(aux,code[2])  
 if code[0] =="b":
   if code[1] == 0:
     return Land(aux,code[2],code[3])     
   if code[1] == 1:
     return Lor(aux,code[2],code[3])  
   if code[1] == 2:
     return Limp(aux,code[2],code[3])
   if code[1] == 3:
     return Labs(aux,code[2],code[3])
   if code[1] == 4:
     return Ax(aux,code[2],code[3])       

def Generate(proof,seq):
 if len(proof) == 0:
  return seq
 newseq = copy.deepcopy(TreeCodeApply(proof[0],seq))
 return Generate(proof[1:],newseq)
 
def DisplayLinear(seq):
 for p in seq.collection:
  print(str(p.id) +". " + p.display() + "   " + str(p.parent) )     



def Prove():
 global State 
 x = search(State)[1]   
 RulesDisplay(x)
 print("")
 DisplayLinear(Generate(x,State)) 
        
     
         

            
            