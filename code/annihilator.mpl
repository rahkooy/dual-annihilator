##
##   This is an aextended and development on top of of the following,
##   for computing the recurrence relations of a given multi-dimensional sequence
##   The original code computes the dual of an m-primary ideal. 
##   Hamid.Rahkooy@maths.ox.ac.uk, 2024, Oxford
##   =============================================================
##
##   ORIGINAL CODE:
##
##    Title: 	mroot - Multiple Roots and primal-dual structure
##    Authors: 	Angelos Mantzaflaris <Firstname.Lastname@oeaw.ac.at>
##              Bernard Mourrain     <FirstnameLastname@inria.fr>
##
## 2010-2012
## See A.M. & B.M., `Deflation and Certified Isolation of Singular
## Zeros of Polynomial Systems`
##
## Last Modification: 7/2012 
##
## ----------------------------------------------------------------------

annihilator:=module()

export
hankel,
multvar_hankel,
monomials,
border,
auto_red,
notdivM,
nilindex,
ann_N,
moncoeff,
coeffof,
minpoldeg,
findzeromon,
killmon,
cand_ann,
int_i,
diff_scale,
conds,
initann,
ann_topdown,
first_comb,
next_comb,
lstcoefof
;

option package;

use LinearAlgebra in
use Groebner in
use ArrayTools in
#====================Univariate Sequence=====================================================
#====================================================================================
#=======Sequence given as list l=(l[i]), even length s
# H Hankel matrix of size s/2*s/2
# Ker H = annihilator of deg <=  #s/2
hankel:=proc(l::list) 
   local s,l0,i,hrow,j,h,H,lh,MM;  #CHECK Why localizing gives error----
   with(LinearAlgebra):
   s:=nops(l);  #length of l
 #--------------------adding s times0 to l: kernel empty!! CHECK THE PAPERS--------
   #l0:=l;
   #for i to s do
     #l0:=[op(l0),0];
   #end do;
   #print(l0);
#--------------------Initialize H with H=l, as its first row--------------
   lh:=[];
   for i to s/2 do
     lh:=[op(lh),l[i]];
   end do;  
   H:=Matrix(lh);
#-----------Compute h[i+1], i>=2th row of H and stack them to H-------------
   for i to (s/2) do  
      hrow:=[];
      for j to s/2 do
        hrow:=[op(hrow),l[i+j]];
      end do;
      h[i+1]:=Matrix(hrow);
      H:=<H;h[i+1]>;      
   end do;
   print("H=",H);
#--------------------Computing Kernel of the Hankel Matrix-----------------------
   print("Ker(H)=",NullSpace(H));
end proc:
#=============

#====================================================================================
#====================================================================================
#=======Multivariate Sequences/hankel matrices, Using Table==========================
#====================================================================================

multvar_hankel:=proc(l::table,var::list) 
#Input: 
    #l given as table, e.g., 1=3,x=1,...x^iy^j=3,...
    #l given WITH its border
local H,M,m,t,m_l,mm_l,K,v,f,MM,ann,Mborder,Mlist,Mandborder, redann, num;

#with(LinearAlgebra):
H:=Matrix(); #Hankel matrix-----
M:={indices(l,'nolist')}; #monomials indexing columns----------
#print("Indexing Monomials=", M); 
Mborder:=border(l,var);
#print(Mborder);
Mandborder:=M union Mborder;
#print(Mandborder);

#constructing row m*l of Hankel matrix-------
  for m in M do 
   m_l:=[];
    for t in M do
      if m*t in M then
       m_l:=[op(m_l),l[m*t]];
      else m_l:=[op(m_l),0];
     fi;
     #print("Kernel(H)=", m_l);
    od; 
  mm_l:=Matrix(m_l); #row m*l of H
  #print(m, mm_l);
  H:=<H;mm_l>; # concatenating row m*l to the Hankel matrix------
  #print(H);
 od;
 #print("H=",H);
 print("size of hankel mat=", Dimension(H));


#kernel of the Hankel matrix H----
 K:=NullSpace(H); 
 #print("Ker(H)=", K);

#Convert Kernel of H into Annihilator----
 Mlist:=convert(M,list);
 MM:=Matrix(Mlist);
 ann:={};
 for v in K do
  f:=MM.v; 
  ann:=ann union {f[1]}; #ann is a list, but f is a matrix...change needed...
 od;

#Auto-Reduce
redann:=auto_red(ann);
num:=nops(redann);

#Add border of M to ann
#ann:=ann union Mborder;

#print("Annihilator via Hankel Matrix=",ann);
print("red Hankel=", redann, "#red ann=", num),
#print("Hankel=",ann), 
print("red border=",Mborder);
end proc:
#================


#====================================================================================
#====================================================================================
#=======Integration for Annihilator==========================
#====================================================================================
#Setting:
#monomials:=proc(l::table,var::list)
#border:=proc(l,var) a SET
#auto_red:=proc(s::set)
#nilindex:=proc(l::table,var::list), largest degree monomials in the border of M
#ann_N:=proc(l::table, var::list)
#Output: SET of annihilators of deg N
#moncoeff:=proc(P, var, t): coeff of mon t in pol p
#coeffof := proc(m,p,vvar)
#minpoldeg:=proc(l::table,var::list)--Output: dm=[d,m]: d deg list of min pols; m: mon #divided by every mon--d_i=max deg_i -1??? or deg_i??
#findzeromon:=proc(l::table,var::list): Find mons in S:=M/T=[S1,...Sn union border]
#killmon:=proc(l::table, var::list,p::polynom)---[b(x)|S_1<>0,...,b(x)|S_n<>0]
##cand_ann:=proc(l,var,annt):---
#input: annt, deg=>N-t annihilator
#output: [lambda,L,b], where
        # lambda=[lambda_1,...,lambda_s]
        # L=[d_1b_1|S_1,...d_nb_s|S_n]
        # b=sum lambda_i d_kb_j|S_k
#int_i:=proc(l::table,var::list,p,i)---
#Output: x_i*p mod M union border of M ----CHECK: M or M union border?
#diff_scale:=proc(p,var,i)
#Input: p: pol, i: number of var
#Output: diff of p wrt var[i] but no change of coeff; e.g. dx(x^2+x*y,[x,y],1)=x+y 
#conds:=proc(l,var,annt) #Input: annt=ann[N-t], degree >=N-t elements of ann
                        #output: M, Matrix of equations of conds i & ii,  
                                 #columns labeled by lambda1,...,lambdas
                                 #first rows corresp to cond i, 
                                 #last rows corresp to cond ii, 
#initann:=proc(l,var)---compute ann_N-1 using hankel matrix
#ann_topdown(l,var): the main procedure

#====================================================================================
#=====================================1--M nonzero monomials================================
monomials:=proc(l::table,var::list)
local n,M;
M:=[indices(l,'nolist')]; #nonzero monomials; BORDER NOT INCLUDED---
#print("Monomials, M=", M); 
end:
#===============================
#===============================border of M==========================================
#ouput: SET of border elements of M, monomials indexing l==NOTE: output is a SETTTT
border:=proc(l,var)
local M,Mset,n,xiM,Mplus,Mborder,i,m, redborder;

M:=monomials(l);
n:=nops(var);
xiM:={};
Mplus:={};
Mborder:={};

#Convert list M into set:
Mset:={};
for m in M do
   Mset:={op(Mset),m};
od;
#print(Mset);

for i to n do
   for m in Mset do
       xiM:=xiM union {m*var[i]}; # Compute \cup x_i*M
   od;
   Mplus:=Mset union xiM; # Border of M = \cup x_i*M \setminus M
od;
Mborder:=Mplus minus Mset;
redborder:=auto_red(Mborder);  #Auto-reduce Border alements
   
#Mborder, 
redborder;
#print("Mborder",Mborder, "reduced Border=, redborder);
#print("Mborder",Mborder);
end:
#===============================
#===================Auto-reduce members of a set/ideal of polynomials
#==========================
auto_red:=proc(s::set)
local p, q, red;

 red:=s;
  for p in s do
     for q in red minus {p} do
        if divide(p,q) then 
           red:=red minus {p}
        fi;
     od;
  od;

red;
end:
#===============================
#===================NOT USED==mon of M not divisible by anything==========================
notdivM:=proc(l,var)
local M,Mset,m,notdivM,M1,t;

M:=monomials(l,var);
#Convert list M into set:
Mset:={};
for m in M do
   Mset:={op(Mset),m};
od;
#print(Mset);

notdivM:={};
for m in Mset do
#   print("m",m);
   M1:=Mset minus {m};
   t:=M1[1];
#   print("t",t);
   while not divide(t,m) do
        M1:=M1 minus {t};
#        print("M1new",M1);
        if M1<>{} then          
               t:=M1[1];
        else break;
        fi;
#        print(t);
   od;
   if M1={} then
      notdivM:={op(notdivM),m};
   fi;
   
od;

notdivM;
#print("mon not divisible by M",notdivM);
end:
#===============================
#=====================================2--N nil-index======================================
nilindex:=proc(l::table,var::list)
#OUTPUT: largest degree monomials in the border of M
local degM, m, N,M,Mborder;
M:=monomials(l,var); 
Mborder:=border(l,var);
#print("M=",M);
degM:=[]; #list of degrees of mon in border of M
for m in Mborder do
#print(m);
 degM:=[op(degM),degree(m)]; 
 #print(degM);
od;
N:=max(degM); 
#print("Nil-index=",N);
end:
#===============================
#====================================3-Initiate ann_N= deg N monomials in M================
ann_N:=proc(l::table, var::list)
#Output: SET of annihilators of deg N
local N,M,m,initial_ann,Mborder;

initial_ann:={};
M:=monomials(l,var);
Mborder:=border(l,var);
N:=nilindex(l,var);
for m in Mborder do
 if degree(m)=N then 
  initial_ann:={op(initial_ann),m}; 
 fi; 
od;
initial_ann;
#print("ann_N=",initial_ann);
end:
#===============================
#====================Find Coeff of a mon in a pol-Alg1-============================
moncoeff:=proc(P, var, t)
local L, H, i, k:

L:=[coeffs(P, var, 'h')]: H:=[h]: k:=0:
for i from 1 to nops(H) do
 if H[i]=t then k:=L[i] fi:
od:
k;
end proc:
#=====================================================
#====================Find Coeff of a mon in a pol-from DUAL PACKAGE-===============
#Return the coeff. of p in variables var of the monomial m
#(from multires)
coeffof := proc(m,p,vvar)
local i,zs,lm,lc,k;
#    if m=0 then return 0;fi;
  lc := [coeffs(p,vvar,'lm')];
  lm := [lm];
  if member(m,lm,'k') then lc[k] else 0 fi;
end:
#=====================================================

#====================================4--min pol degrees & m=x^alpha=========================
#####Input: multi-seq and var;
#####Output: dm=[d,m]: d deg list of min pols; m: mon divided by every mon
minpoldeg:=proc(l::table,var::list)
local partdegM,d,m,u,M,i,n,dm,Mborder;

n:=nops(var);
M:=monomials(l,var);
Mborder:=border(l,var);
d:=[]; # d[i] deg of min pol of var[i]
m:=1; # monomial divided by all monomials in M

for i to n do
  partdegM:=[]; # partial deg of mono in M=max deg in border
  for u in M do    #==M or Mborder?
     partdegM:=[op(partdegM),degree(u,var[i])]; 
  od;
  #d:=[op(d),max(partdegM)];                #===d_i=deg min pol xi
  d:=[op(d),max(partdegM)];               #===d_i=deg min pol xi-1???
  m:=m*var[i]^(d[i]); 
od;

dm:=[d,[m]]; # OUTPUT: put d and m in a table
#print("partial degrees:",d);
#print("m=",m);
end:
#===============================
#====================================5--Find mons in T:=[m/T_k] OR S:M/T==================
#==========NEEDS RE_WRITING...CHECK PDF FILE=======
findzeromon:=proc(l::table,var::list)
local M,m,Mset,Mborder,MM,d,S,i,n,j,vari,x,Si;
#T,T_kk,S_kk,k,u,Ti,S_i,SS,TT,Tinit,Sinit

M:=monomials(l,var);
#Convert list M into set:
Mset:={};
for m in M do
   Mset:={op(Mset),m};
od;
#print(Mset);

Mborder:=border(l,var);
MM:=Mset union Mborder;
d:=minpoldeg(l,var)[1];
#print(MM);
#print(d);
n:=nops(var);

#------Option 0: S[i]={m in MM| x_i+1^d_i+1...x_nd_n diveds m}------
S:=[];
for i to n-1 do  #go till S_n; S_n=M to be added at the end
   vari:=seq(var[j]^d[j],j=i+1..n);  
#print("powers of vars",vari);
   x:=convert([vari],`*`);  #x = product x_i+1^d_i+1...x_nd_n
#print("product=x=",x); 
   Si:={};
   for m in M do             #CHECK AGAIN: M or MM=M union border
       if divide(m,x) then     
#print("m",m);
          Si:=Si union {m};
#print("Si",Si);
       fi;
   od;
   S:=[op(S),Si];
#print("S",S);
od;
S:=[op(S),MM];     #Add S_n=MM to S
#-----------
##====OPTION 1:Compute Tinit:=[T_kk] mons in M with deg_k<d_k for fixed k
##====OPTION 2:Compute Sinit:= mons in M with deg_k=d_k for fixed k
##Tinit:=[];
#Sinit:=[];
#for k to n do
# # T_kk:={};
#  S_kk:={};
#  for u in MM do
##   print(u); print(degree(u,var[k]));
# #  if degree(u,var[k])<d[k] then 
#  #    T_kk:={op(T_kk),u}; #SET of mono with deg_k<d_k
#    if degree(u,var[k])=d[k] then 
#      S_kk:={op(S_kk),u}; #SET of mono with deg_k=d_k
#    fi;
##    print("T_kk=",T_kk);
##    print("S_kk=",S_kk);
#  od;
##  Tinit:=[op(Tinit),T_kk]; 
#  Sinit:=[op(Sinit),S_kk]; 
#od;
##print("Tinit=",Tinit);
##print("Sinit=",Sinit);
#
##Compute T=[m/T_k = union(T_kk,...,T_nn)]
##Compute S=[union(S_kk,...,S_nn)]
##T:=[];
#S:=[];
#for i to n do
##TT:={}; #is for m/T_k
#SS:={}; #is for MM \ m/T_k
#  for j from i+1 to n do
# #     TT:=TT union Tinit[j]; # THEREFORE: TT=m/T_i=[T_ii union...union T_nn]
#      SS:=SS union Sinit[j]; # THEREFORE: SS=M \ m/T_i=[SS_ii union...union SS_nn]
##     print("TT",TT);  
##     print("SS",SS);  
#  od;
##  T:=[op(T),TT];  # T=[m/T_1,...,m/T_n], NOTE: m/T_i is a SET
#  S:=[op(S),SS];  # S=[M\m/T_1,...,M\m/T_n], NOTE: M \ m/T_i is a SET
##  print("T=",T);
##  print("S=",S);
#od;
#
##T;
#S;
##print("T=",T);
##print("S=",S);
#

end:
#===============================
#=================6--compute b(x)|m/T_k=0 OR b(x)|S_k<>0================================
#-----find support of b, then check in m/T_k
killmon:=proc(l::table, var::list,p::polynom)
local M,T,S,n,plist,i,Ti,Si,pi,m,s,cs;

M:=monomials(l,var);
#T:=findzeromon(l,var);
S:=findzeromon(l,var);
#print(S);
n:=nops(var);

#create a list of n copies of p, in i-th copy m/T_i(S_i) to be killed(survived)
plist:=[];
for i to n do
    plist:=[op(plist),p];
od;
#print("initial plist",plist);

for i to n do
 #   Ti:=T[i];
#    Si:=S[i];
    pi:=plist[i];
   #print(pi,S[i]);    ###BORDER IS THE PROBLEM....
       for s in Support(pi) do
           if not s in S[i] then
 #     for m in T[i] do
   #         if s=m then pi:=pi-s; fi;
                cs:=moncoeff(pi,var,s); #Find Coeff of s in pi
                pi:=pi-cs*s;
            fi;
#         od;
      od;
    plist[i]:=pi;
od;

plist;
end:
#===============================
#=================7-Candidate ann; b(x)=sum lambda_jk diff_k(bj)========================
cand_ann:=proc(l,var,annt) 
#input: annt, deg=>N-t annihilator
#output: [lambda,L,b], where
        # lambda=[lambda_1,...,lambda_s]
        # L=[d_1b_1|S_1,...d_nb_s|S_n]
        # b=sum lambda_i d_kb_j|S_k
local sd,killb,d_kb_j,j,k,n,diffkillinit,candid,v,b,lambda,s,t,L,M,m,initd_kb_j,w,nonZeroIndices;

M:=monomials(l,var);
n:=nops(var);
sd:=nops(annt);
#compute list of bj(x)|m/T_k=0 OR bj(x)|S_k<>0
killb:=[seq(killmon(l,var,annt[j]),j=1..sd)];
#print("bj|Sk",killb);

# d_kb_j|S_k, i.e., Coeff of Vector Lambda
d_kb_j:=[];
for j to sd do
    diffkillinit:=[];
    for k to n do
       #if degree(killb[j][k],var[k])<>0 then          
        initd_kb_j:=diff_scale(killb[j][k],var,k);   #Scaled diff if deg<>0
        #print("scaled diff",initd_kb_j);
      # else initd_kb_j:=diff(killb[j][k],var[k])
       #fi;
        for m in Support(initd_kb_j) do    #Kill mon not in M
           if not m in M then
              initd_kb_j:=initd_kb_j-m*moncoeff(initd_kb_j,var,m);
           fi; 
        od;
        diffkillinit:=[op(diffkillinit), initd_kb_j]; 
         #d_k bj|m/T_k; Gives list of coeff of lambda_jk
    od;
     d_kb_j:=[op(d_kb_j),diffkillinit];
od;
#print("d_k(b_j|S_k)",d_kb_j);

#Convert d_kb_j into one list: (REMOVING ZEROS)
#L=[d_1(b_1|S_1),...,d_1(b_sd|S_1),...,d_n(b_1|S_n),...,d_n(b_sd|S_n)]
L:=[];
w:=nops(d_kb_j);
for t to w do
          L:=[op(L),op(d_kb_j[t])];
od;
#print("one list of d_kb_j instead of nested list",L);

##REMOVE ZEROS FROM L AND CALL IT nonZeroIndices ?????? MESSES UP W COND i
#nonZeroIndices := [seq(`if`(L[i]=0,NULL,L[i]), i=1..nops(L))];
#L:=nonZeroIndices;
##print("nonzero",nonZeroIndices);

# s= number of all d_kb_j|S_k = #??nonzero elemetns of L???
s:=nops(L);
#print("s=#dkbj=#L",s);


#build lambda=[lambda1..lambdas], which is actually listing [lambda_jk] in one index
lambda:=[cat(lambda,1..s)];     
#print("lambda",lambda);

#construct b=sum lambda[i]*L[i] and bl=sum lambda[i]*l(L[i])
#Do we really need to construct b? OR just bl is enough???????????
b:=0;
for v to s do   
   b:=b+ lambda[v]*L[v];  
   #print("nonzero Lv",L[v]);
od;
#print("b",b);
#--------------

candid:=[lambda,L,b];
end:
#=====================================
#========================9-Lex-first r-combination of [1..n]: For 1<k<l<n===============
#-------Taken From Dual Package------
# nops(c)----------in our case r=2
first_comb:= proc(n::integer,r::integer)
if r<=n then
   return [seq(1..r)];
else
    #print(`Warning: r>n combination requested`,r,n);
    return NULL;
fi;
end:
#======================================
#=====================10-Next r-combination of [1..n] after c in lex-order-For 1<k<l<n=========
#-------Taken From Dual Package------
# nops(c)=r----------in our case r=2; actually: c=[k,l]
next_comb := proc( c::list, n::integer)
	  local nc,r,i,j;
	  r:= nops(c);
	  if c=[seq(n-r+1..n)] then return NULL; fi; #finished
	  nc:=c;
	  i:=r;
	  while c[i]=n-r+i do
	  	i:=i-1;
	  od;
	  nc[i]:=c[i]+1;
	  for j from i+1 to r do
	     nc[j]:= nc[i]+j-i;
	  od;
nc;
end:
#======================================
#======================8-Integration wrt x_i mod M===============================
int_i:=proc(l::table,var::list,p,i)
#Output: x_i*p mod M union border of M ----CHECK: M or M union border?
local n,M,m,intipmod,intip,Mborder,Mset,MM;

M:=monomials(l,var);
#Convert list M into set:
Mset:={};
for m in M do
   Mset:={op(Mset),m};
od;
#print(Mset);

Mborder:=border(l,var);
MM:=Mset union Mborder;
n:=nops(var);

intip:=integrate(p,var[i]); #Integrate
intipmod:=intip;
for m in Support(intip) do
    ##Kill mons in the border of M:-->not enough if we integrate mon in border 
    #if m in border(l,var) then   
    #Kill mons m not in M:
    if not m in M then        #----CHECK: M or MM=M union border?
       intipmod:=intipmod-moncoeff(intip,var,m)*m; 
       #print(intipmod);
    fi;
od; 

intipmod;
end:
#===============================
#===============List of coeffs of a pol wrt an order==============================
#---------------Borrowed from Dual Package--------------------------------
lstcoefof := proc(p,var)
local lm,r,c;
  lm := NULL;
  r := sort(p,var,tdeg);
  while r <> 0 do
     c := tcoeff(r,var,'m');
     lm := lm, c;
     r := expand(r-c*m);
  od;
  lm;
end:
#=====================================
#========================Differentiate with scaling========================
diff_scale:=proc(p,var,i)
#Input: p: pol, i: number of var
#Output: diff of p wrt var[i] but no change of coeff; e.g. dx(x^2+x*y,[x,y],1)=x+y 
local diffp,m,cf,mdiv;

diffp:=p;
for m in Support(p) do
    cf:=moncoeff(p,var,m);
    if divide(m,var[i]) then
       mdiv:=m/(var[i]);
       diffp:=diffp-cf*m+cf*mdiv;
    else 
       diffp:=diffp-cf*m;
    fi;
od;

diffp;
end:
#=====================================
#===========================11-Conds (i) & (ii)========================================
#------------------With the help of "mourrain_matrix" in the Dual Package-------
conds:=proc(l,var,annt) #Input: annt=ann[N-t], degree >=N-t elements of ann
                        #output: M, Matrix of equations of conds i & ii,  
                                 #columns labeled by lambda1,...,lambdas
                                 #first rows corresp to cond i, 
                                 #last rows corresp to cond ii, 
local s,lambda,a,c,n,tt1,tt2,p,k,sd,RR,intannt,j,d_kb_j,s1,M,int_l,int_k,var1,rows,R,row,rr,i,L,t,b,v,bl,m,rows_seq,candid;

#print("annt=",annt);
n:=nops(var);
sd:=nops(annt);

candid:=cand_ann(l,var,annt);
lambda:=candid[1];               #====Get lambda from candid ann member
print("lambda",lambda);
s:=nops(lambda);         
#print("s",s);
L:=cand_ann(l,var,annt)[2];      #====Get L, list of nonzero dkb_j|S_k
print("L=[d_kb_j]",L);
b:=cand_ann(l,var,annt)[3];      #====Get b= sum lambda.d_kb_j|S_k===REALLY NEEDED????
print("b",b);

#--------Cond ii----
bl:=0;
for v to s do   
   for m in Support(L[v]) do
       if m<>0  then
#          print("m",m);
          bl:=bl+ lambda[v]*l[m] * moncoeff(L[v],var,m); #COEFF NEEDED
       fi;
   od;
od;
print("pol of cond ii, bl ",bl); 
#bl to be added to the array rows, of equations of cond i below
#------------------

#---------Cond i----
c:=first_comb(n,2);   #combinations of 1<=k<l<=n, starts with c=[k=1,l=2]
#print("initial k,l",c);

RR := NULL;           #NEVER USED--WHAT IS THIS? IS NOT IN mourrain_matrix, but in  mourrain_step

while c <> NULL do
        int_l:= [seq(int_i(l,var,annt[j], c[2]),j=1..sd)];#int_l(bj)
        print("int_1(bj)",int_l);
        int_k:= [seq(int_i(l,var,annt[j], c[1]),j=1..sd)];#int_k(bj)
        print("int_k(bj)",int_k);
        
        #p: pol of cond i
        p:=0; 
        for j to sd do
            #print(j);
            p:= p + lambda[ (j-1)*n + c[1] ] * int_l[j]
                  - lambda[ (j-1)*n + c[2] ] * int_k[j];
            #print("p",p); 
        od;

##Below lines checks if p=0, then it goes to the next k<l, 
##without building the matrix; This causes ignoring the second condition.
##It is commented, and instead while building the matrix, it throws away zero rows.
#        if p=0 then      # gives no equation
#            c:=next_comb(c,n);         
#            next;
#        fi;
        
         p := expand(p); 
         print("pol of Cond i=",p); 

         #-----Building Array of Conds i & ii----
         #COND i: Collect coeff of p = linear equations in lambdai && COND ii: bl=0
         rows_seq:=lstcoefof(p,var),bl; 
         rows:= Array([rows_seq]); 
         #print("rows",rows);
         
         #--------------------
         #Needed to construct p? 
         #Maybe enough to collect coeff of lambda_jk, i.e., 
            #Constructing List of all integrations=coeff of lambda_jk=
            #[int_1(b1)..int_n(b1)...int_n(b_sd)..int_n(b_sd)]
            #In order to pick lambda_jl & lambda_jk for cond (i):
        #int_seq:=[];
        #for j to sd do
             #p:=annt[j]; 
             #print(p);
             #intannt:=seq(int_scale(l,var,p,i),i=1..n);
             #int_seq:=[op(int_seq),intannt];
        #od;
        #print("[int_1(b1)..int_n(b1)...int_n(b_sd)..int_n(b_sd)]",int_seq);

        #-------------Matrix of conds i & ii--------
        R:=NULL;  #seq of coeff of equations of conds in vars lambda
        for row in rows do
            rr:= Array([seq(0,u=1..s)]); #lists don't work for big dimension
            for i to s do
                #print(row);
                rr[i]:= coeffof(lambda[i],row,lambda); # could use moncoeff(p,var,t) too
            od;
            R:=R, convert(rr,`list`); 
        od;

        if R<>NULL then
       #     M:= Matrix(<Matrix([R]), M> );  # Don't know why Dual Package needs to start with
                                             # M:=Matrix(1,nops(L));
             M:= Matrix([R]);
            #print("Matrix of cond i & ii, columns labeled by lambda",M);
        fi;
       #-----------------------------

    c:=next_comb(c,n);
    #print(c);
    od;  #End of while loop: all combinations of k<l considered.

M;
end:
#=====================================
#============================Initiate w ann_N-1==========================
initann:=proc(l,var)
local row, m, M, N,mat,K,v,ann,f,monrow,monmat;

M:=monomials(l,var);
N:=nilindex(l,var);
ann:={};

#construct Hankel matrix with one row, of deg N-1 mons-------
row:=[];       #row of hankel mat with values of mon deg N-1
monrow:=[];    #list of mon of deg N-1
for m in M do 
   if degree(m)=N-1 then
      row:=[op(row),l[m]];
      monrow:=[op(monrow),m];
   fi;
  mat:=Matrix(row);
  monmat:=Matrix(monrow);
od;
print("mat N-1",mat);
#print("matrix of mons",monmat);
#Compute kernel and convert into ann_N-1----
 K:=NullSpace(mat); 
 #print("Ker(mat)=", K);
 for v in K do
  f:=monmat.v; 
  ann:=ann union {f[1]}; #ann is a list, but f is a matrix...change needed...
 od;

ann;
end:
#============================
#=============================Main Procedure====================FIXING NEEDED===============
ann_topdown:=proc(l::table,var::list) 
#l given as above; , var:list of variables----
#Output: ann, the SET of annihlators
local M,ann,i,annt,old_ann,K,MM,v,f,new_ann,Mborder,Mat,m,N,L;

N:=nilindex(l,var);
print("nilindex=",N);
M:=monomials(l,var);         #==NEEDED? USED AT ALL?
Mborder:=border(l,var);

#1-Initiate with ann_N or ann_N-1=====CHECK: perhaps CANNOT get ann_N-1 from ann_N 
                                #=====OR makes next step matrices huge?

#--Option 1: ann_N
ann:=ann_N(l,var); 
#--Option 2: compute ann_N-1 and initiate with that
#ann:=initann(l,var);  #MUST add ann_N, i.e., ann:=initan(l,var) union ann_N(l,var);
print("initial ann",ann);


#2-derivation step 
for i from N-1 to 1 by -1 do  #Go till deg 1; 
                              #deg 0 mon is 1, which almost never appears m-primary ann
      new_ann:={};
      old_ann:=ann;              #Set old_ann:=ann_N union .. union ann_N-i
      #print("old ann",old_ann);
      Mat:=conds(l,var,old_ann); #Apply Conds i & ii and build Matrix Mat     
      print("Matrix", Mat);
      K:=NullSpace(Mat);         #Compute kernel of Mat
      print("Ker(Mat)=", K);

      #Convert Ker(Mat) into annihilators
       L:=cand_ann(l,var,old_ann)[2];
       print("L=[d_kb_j|S_k]",L);
       MM:=Matrix(L);   #convert L=[d_kb_j|S_k] into a matrix
       for v in K do
             f:=MM.v; 
             print("freshly computed ann member:", f[1]);
             if f[1]<>0 then             #How to avoid producing zeros at the beginning?
                new_ann:=new_ann union {f[1]}; #new_ann is a list, but f a matrix...fix it..
             fi;
       od;

#    #Add deg i members of the border of M to new_ann:---ADD at the end
#        for m in Mborder do
#           if degree(m)=i then
#              new_ann:=new_ann union {m};
#           fi;
#        od;

    ann:=ann union new_ann;    #add new ann to existing ann
    #print(ann);
od;

ann:=ann union Mborder;       #Add border elements to ann at the end
#print("Final Ann=",ann);

end:
#================

#====END USE===
end use;
end use;
end use;

#====END MODULE===
end module:
