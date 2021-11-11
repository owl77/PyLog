import parser
import tokenizer
import astop
import pickle
import copy
import os


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
          seq.proof.append("rand(" + str(n) +")")
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
           seq.proof.append("ror1(" + str(n) + ")")
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
           seq.proof.append("ror2(" + str(n) + ")")
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
            seq.proof.append("rimp(" + str(n) + ")")
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
            seq.proof.append("land(" + str(n) + "," + str(m)+ ")")
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
            seq.proof.append("lor(" + str(n) + "," + str(m)+ ")")
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
            seq.proof.append("limp(" + str(n) + "," + str(m)+ ")")
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
           seq.proof.append("labs(" + str(n) + "," + str(m)+ ")")
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
           seq.proof.append("ax(" + str(n) + "," + str(m)+ ","+ form +")")
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
            
            
            
            