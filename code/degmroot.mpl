##
##   This is an aextended and development on top of of the following in order to compute  the dual of an arbitrary ideal (NOT necessarily m-primary) 
##   UP TO A GIVEN DEGREE
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


#
# The module degreemroot
#
degmroot := module()


############################################################
###-------------------- SECTIONS------
#-Algorithms
#-Operators on Differentials
#-Applications
#-Deflation
#-Benchmark
#-Setting and procedure analyser
############################################################


export
############################################################
##---------------------PROCEDURES LIST---------
##=====================NEEDED====================
# Dual Basis computation
macaulay_block, cand_set,
macaulay_step, mourrain_step,
#Macaulay's method
macaulay0,
macaulay,
# Integration method
mourrain0,
mourrain,
hilbert_func,

#reciprocal of generating function---NEW
gen, 
rec,
largest_mon,
rec_list,
rec_dual,
border,
monomials,
indexmon,
rec_gen,
auto_red,
mondegd,
mondeg,
badmon,
randseq,

#Combinatorics
first_comb, next_comb,
first_mon, next_mon,
mac_dim, int_dim,

# Operations on polynomials
coeffof,lstcoefof, lstterms,
lstmonof, lstmonsof,exp_of,
dual_monomial, add_noise,
diff_poly, diff_system,
#Operations on matrices
dmatrix2diffs, matrix2polys, matrix2diffs,
rmaximal_minor, cmaximal_minor,
nkernel, ncorank, m_inverse,

# Operations on differentials
has_term, add_df, sadd_df, sub_df,
remove_zero,sremove_zero,
to_function,
to_polynomial,to_monomial,
refine_basis, symb_diff,
int_df, diff_df,
scalar_df, coefmatrix,
add_var, symbolic_dual,
parametric_basis,
generic_dual,
unify_coef, uadd_var,

# lex-ordering on differentials
rlex_c,grlex_c,grlex_df,lex_c, lex_df,
rlex_min,total_deg, leading_df, trailing_df,

# Operations in the quotient
normal_form, mult_table, mult_mat,

##=========================================
#local
# Deflation
deflate, deflate_lin, deflate_incr, deflate_lvz,
deflate_only, deflate_hint,
new_system,new_system1,new_system2,#--------------------------------?
deflate_system,new_system4,
get_system,#--------------------------------?
pert_poly, pert_system, pert_point,
#Newton's method
newton, newton_mod,
newton_next, newton_step,
#Interval arithmetic operations
mat_add,mat_sub,mat_prod,
eval_on_ints,istart,iend,
X_xs,i_box,mbox,dom_size,
dom_center, inclusion,
# Auxiliary#--------------------------------?
check_list, get_var, rump,
sign_of, app_funct,
#Tests#--------------------------------?
bench_systems, run_tests,
cyclicn, kssn, expmultn,
#Experimental#--------------------------------?
make_basis_pair,
dual_constraints_1, closedness_equations,
delta,
# New stuff 2015#--------------------------------?
kernelToDifferentials,
kernelCoefMatrix,
mourrain_matrix,directionalMult,directionalMult2,
dualBasisNew,
mourrain_matrix_new,
# rev-lex compare on differentials----------------------------?
rlex_df,
# Topological degee computation----------------------------?
topological_degree,
# Implicit curve branches computation
curve_branches,
# Certify root in domain
certify_root,
# Compute primal-dual orthogonal pair----------------------------?
basis_pair,
# Apply Rump's test
rump_test,
rump_iter
;

############################################################
##-END     --------------------PROCEDURES LIST---------
############################################################


option package;

############################################################
### Packages: Linear Algebra & Groebner 
############################################################
use LinearAlgebra in
use Groebner in
use ArrayTools in
#use PolynomialIdeals in
use RandomTools in

########################################################
########################################################
#### Macaulay & Mourrain's Algorithms
########################################################
########################################################

#
# Macaulay's matrix dimension for s eq in n vars in depth dp
#
mac_dim:= proc(s::integer,n::integer,dp::integer )
    s*binomial(dp-1+n,dp-1), binomial(dp+n,dp);
end:

#
# Bound on integration method matrix dimension for s eq in n vars in depth dp
#
int_dim:= proc(s::integer,n::integer,dp::integer, mult::integer )
    #binomial(n,2)*binomial(dp-2+n,dp-2)+s, mult*(n-1)+1;
    mult*binomial(n,2)+s, mult*(n-1)+1;
end:


#
# Step in depth dp of Macaulay's method for the dual basis
#
macaulay_step := proc(f::list, var::list, z::list, dp::integer, tol:=0, BB:=[], last::integer:= -1)
local E, n,NN,R,p,row, r, c, M, mc, j, ci, mr, k, ri, i, t;

    n:= nops(var);
    if dp<0 then return [0]; fi;
    if dp=0 then return [Matrix(<seq(0,s=1..n),1>)]; fi;

    r:= nops(f)*binomial(dp-1+n,dp-1);
    c:= binomial(dp+n,dp);
    NN:=[seq(0,s=1..n)];
    mc:=1;
    if BB<>[] then #MM2011
        c:= c-nops(BB);
        mc:=0;
        NN:=NULL;
    fi;

    M:= Matrix(r,c);
    E:= exp_of(BB,var);
    for j to dp do#depth
        ci:= first_mon( j , n);
        c:=0:
        while ci<>NULL do #order of diff(column)
            if BB<>[] and member(ci,E) ## MM2011
            then
                ci:= next_mon( ci , j);
                next;
            fi;
            c:=c+1;
            NN:=NN,ci;# keep column indices
            mr:=0;
            for  k to j do#multiplier degree+1
                ri:= first_mon(k-1, n);
                r:=0:
                while ri<>NULL do#multiplier monomials
                    r:=r+1;
                    for i to nops(f) do# f_i
                        t:=diff_poly(
                            mul((var[s]-z[s])^ri[s],s=1..n)*f[i],
                            var, Matrix(<op(ci),1>) );
                        #print(`at`,mr + i,mc + c);
                        M[mr + i,mc + c]:=
                        eval(t,[seq(var[s]=z[s],s=1..n)]);
                    od;
                    mr := mr+ i-1;
                    ri:= next_mon( ri , k-1);
                od;
            od;
            ci:= next_mon( ci , j);
        od;
        mc:= mc + c; #loop ends in c-value Ok
    od;
    c:= Dimension(M)[2];

## Condition (iii) MM2011
    c:=NULL;
#    if BB <> [] then
#        R:=NULL;
#        c:=NULL;
#    fi;

    R:= nkernel( M , tol);
    #print("Mac. Dimension:",Dimension(M), R);

    if (nops(R)=0 or nops(R)=last) then
        print("Macaulay matrix size = ", Dimension(M) );
    fi;

    p:=NULL;
    for row in R do
        #M:=NULL;
        M:=Matrix(n+1,1);

        for i to nops([NN]) do
            if tol=0 or abs(evalf(row[i]))>tol then
                t:= Matrix(<op(NN[i]),row[i]>);
                #M:=M, t;
                M:=add_df(M,t, tol);
            fi;
        od;
        p:= p, Matrix([M]);
    od;

#sort([p], proc (a, b) options operator, arrow;not Groebner:-TestOrder(a, b, grlex(op(var))) end proc);
# sort([p], rlex_df ); # sorting spoils primal-dual pairs
[p];
end:

#
# Step of the Integration Method given partial dual basis DD
# and (optionally) partial standard basis BB of the quotient
#


###---------------------------------------NEW------------------------
# Representing Sequence as a Differential Polynomial
#
gen:=proc(l::table)
    local ind,entry,genfun;
    ind:=Matrix([indices(l,'nolist')]); 
    entry:=Matrix([entries(l,'nolist')]);
    genfun:=ind.Transpose(entry);
    
genfun(1,1);    
end;

###---------------------------------------NEW------------------------
# Polynomial Representing index monomials of the Sequence
#
indexmon:=proc(l::table)
    local ind,e,s,poly;
    
    ind:=Matrix([indices(l,'nolist')]); 
    s:=nops([indices(l,'nolist')]);
    e:=Matrix([seq(1, j=1..s)]); 
    poly:=ind.Transpose(e);
    
poly(1,1);    
end;

###---------------------------------------NEW------------------------
# Largest Monomial Divided by Every Monomial in a Polynomial
#
largest_mon:=proc(p,var::list)
   local n,i,xalpha;
   n:=nops(var);
   xalpha:=1;
   for i to n do
     if degree(p,var[i])<>0 then
        xalpha:=xalpha*var[i]^ (degree(p,var[i]));  
     fi;
   od;

xalpha;
end:

###---------------------------------------NEW----------------------
# Auto-Reduce Annihilator, i.e., keep co-prime pols
#
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


###---------------------------------------NEW----------------------
# Reciprocal of a Polynomial
#
rec:=proc(p,var::list)
   local n,L,i,inverseL,recL,xalpha;
   n:=nops(var);
   inverseL:=p;
   xalpha:=largest_mon(p,var);   
   for i to n do
     if degree(p,var[i])<>0 then
        inverseL:=eval(inverseL,[var[i]=1/var[i]]); 
     fi;
   od;
      recL:=xalpha*inverseL; 

expand(recL);
end:


###---------------------------------------NEW----------------------
# Reciprocal of the Gen Function of a seq 
# Difference with rec(gen(l)):  
#  ----If coeff of largest mon of gen(l)=0, then deg of rec(gen(l)) drops,
#  ----Solution: change xalpha into largest mon in all existing vars, even if the coeff is zero.
#
rec_gen:=proc(l::table,var::list)
   local n,indmi,inverseL,recL,xalpha, g, indm, i;
   n:=nops(var);
   g:=gen(l);
   inverseL:=g;
   indm:=indexmon(l);
   xalpha:=largest_mon(indm,var);
   for i to n do
     if degree(g,var[i])<>0 then
        inverseL:=eval(inverseL,[var[i]=1/var[i]]); 
     fi;
   od;
      recL:=xalpha*inverseL; 

expand(recL);
end:

   

###---------------------------------------NEW------------------------
# Reciprocal of all the Polynomials in Dual of Recip of Gen Fun 
#
rec_list:=proc(l::table, L::list,var::list) #L: list of dual
   local n,i,inversep,recL,xalpha,reclist,m,p,g, indm;
   n:=nops(var);
   g:=gen(l);
   indm:=indexmon(l);
   #xalpha:=largest_mon(g,var); 
   xalpha:=largest_mon(indm,var);
   reclist:=[];
   for p in L do
        inversep:=p;
        for i to n do
           if degree(p,var[i])<>0 then
              inversep:=eval(inversep,[var[i]=1/var[i]]); 
           fi;
        od;
        recL:=xalpha*inversep; 
      reclist:=[op(reclist),expand(recL)];  
   od;  

reclist;
end:


###--------------------------NEW: Taken from annihilator.mpl-------------
# Nonzero monomials in support of the sequence
#
monomials:=proc(l::table,var::list)
   local n,M;
   M:=[indices(l,'nolist')]; #nonzero monomials; BORDER NOT INCLUDED---
   
M;
#print("Monomials, M=", M); 
end:


###--------------------------NEW: Taken from annihilator.mpl-------------TODO: auto-reduce
# Border of Support of Sequence l
# ouput: SET of border elements of M, monomials indexing l==NOTE: output is a SET
#
border:=proc(l,var)
   local M,Mset,n,xiM,Mplus,Mborder,i,m, redborder;

   M:=monomials(l);
   n:=nops(var);
   xiM:={};
   Mplus:={};
   Mborder:={};
   
   #Convert list M into set:
   Mset:={ op(M) };
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
end:

#
###--------------------------NEW--------------------------
# Monomials of degree d not in monomials(l,var)

mondegd:= proc(var::list(name), d::posint)
local T, k, P:= `+`(var[ ]);
   coeffs(expand(P^d), var, T);
   {T}

end proc:


#
###--------------------------NEW--------------------------
#Monomials in given var up to given degee d --- GOOD CODE
#

mondeg:=proc(var::list(name), d::nonnegint)
local n, L;
uses combinat, ListTools;
n:=nops(var);
L:=[seq(map(t->t-~1, Reverse(convert(composition(k+n, n),list)))[], k=0..d)];
map(t->`*`((var^~(t))[]), L);
end proc:

#
###--------------------------NEW --NOT USED--------------------------
#Monomials in given var up to given degee d ----BAD CODE
#

#mondeg:=proc(var::list,d)
#local n, mon, moni, i, j, m1, m;
#
 #  n:=nops(var);
 #  mon:={1};
 #  moni:={1};
 #  for i to d do
 #       for m1 in moni do 
 #            #print(m1);
 #            moni:=moni minus {m1};
 #            #print(moni);
 #            for j to n do
 #               #print(var[j]);
 #                m:=m1*var[j];
 #                moni:=moni union {m};
 #               #print("moni=",moni);
 #            od;
 #       od;
 #       mon:=mon union moni;
 #       #print(mon);
 #  od;
#
#mon;
#end:

#
###--------------------------NEW--------------------------
# Monomials of degree d <= deg(xalpha) not in monomials(l,var)
badmon:=proc(l::table, var::list,dd)
local allmondset, d, j, indm, badmon, m, i, r, deg;
   
   r:=[rec_gen(l,var)]; 
   deg:=degree(r[1]); 
 
   allmondset:=mondegd(var, dd);
   #print("mon up to deg", allmonset);
   
  # find d=[d1,...,dn], degree lists of xalpha 
  indm:=indexmon(l);
  d:=[];
  for j to nops(var) do
    d:=[op(d), degree(indm,var[j])];
    #print("degrees", d);
  od;
 
 # throw in mon of partial deg > d[i]
 badmon:=[];
 for m in allmondset do
      for i to nops(var) do
           if degree(m,var[i]) > d[i] then
               badmon:=[op(badmon),m];
               #print("bad mons", badmon);
           fi;
      od;
 od;
 
# # Throw in reciprocal of mons out of support of l
# supp:=monomials(l,var2);
# print(recoup);
#md:=`union`({1},seq(mondegd(var2,i),i=1..3)) minus {x^3}; 
#badsupp:=md minus {supp[]};
#recbadsupp:=rec_list(l,[badsupp[]],var2);
# 
# badmonfinal:=[op({badmon[],recbadsupp[]})];

badmon;  
#badmonfinal;
end:

###---------------------------------------NEW--------- Produce random sequence--------
#NEEDS WORK: This only gives values of the sequence on the staircase....----
#Input: a list of pols J, vars; 
#Output: a rational/integer random sequence on quotient wrt tdeg
#
randseq:=proc(J::list, var::list)
   local ideal, n, tord, G, B, b, ratrandoml, intrandoml;
   
   use PolynomialIdeals in
   
   print("NEEDS WORK: This only gives values of the sequence on the staircase, not on M....");

    ideal:=PolynomialIdeal(J); print(ideal):
    n:=nops(var);
    tord:=tdeg(seq(var[j],j=1..n));
    G:=Basis(ideal,tord);
    print(G);
    B:=NormalSet(G,tord)[1];
    #print(B);
    b:=nops(B);
    
#ratrandoml:=table([seq(B[i]=Generate(rational(range=1..5)), i=1..b)]);
#print(ratrandoml);
table([seq(B[i]=Generate(integer(range=1..5)), i=1..b)]);
#print(intrandoml);

    end use;
end:


###---------------------------------------NEW--------- NOTE: IS NOT REDUCED------------
#Dual of reciprocal via different dual algorithms:
#
rec_dual:=proc(l::table, var::list, p::list)
   local L, r, deg, mac0, mac, mour0, mour11, mour15, mour15pol, dann,hann, dualann, 
   s, fullann, b, xalpha, lm, indm, mour, reddualann, t;

   #L:=gen(l); 
   #print(L);
   r:=[rec_gen(l,var)]; 
   #print("reciprocal",r); 
   deg:=degree(r[1])+1; 
   #print("deg of reciprocal+1", deg);
   b:=border(l,var); print(b);
  
  # BEGIN---Check Degenericity:
  # THM. If \ell(xalpha) \ne 0, then ann(\ell) = border
  # Note. \ell(xalpha) \ne 0 iff xalpha \in monomials(\ell)
  indm:=indexmon(l);
  xalpha:=largest_mon(indm,var); 
  #print("mult of lagest partial deg of l= ",xalpha);
  lm:=LeadingMonomial(indm,tdeg(seq(var[i],i=1..nops(var)))); 
  #print("largest mon of l= ",lm);
  if xalpha=lm and l[lm]<>0 then
        dualann:={};
        #print("ann= ",{}, "border=", b);
  else         # END---Check Degenericity:
  
      #Macaulay's method
      #macaulay0( r,var,p,deg):
      #mac0:=to_polynomial(%, dvars);

      #Macaulay's method with MM11 improvement
      #mac:=macaulay( r,var,p,deg):
      #macpol:=to_polynomial(mac[1], dvars);
      #macpol:=to_polynomial(mac[1], var);

      # Integration Method (original)
      #mourrain0( r,var,p,deg):
      #mour0:=to_polynomial(%, dvars);

      #Mourrain's method with MM11 improvement
      mour:=mourrain( r,var,p,deg,l):
      #mour11:=to_polynomial(%[1], dvars);
      mour15pol:=to_polynomial(mour[1], var);
      print("Dual of recip",mour15pol);
   
      # Column removing
      #dualBasisNew(r,var,p,deg):
      #mour15:=to_polynomial(%,dvars); 
      #mour15pol:=to_polynomial(%,var);
      #print(mour15pol);
   
      # List of Reciprocals of Dual Elements
      dann:=rec_list(l,mour15pol,var);
      #dann2:=rec_list(l,macpol,var);
      #print("ann which is a subset rec of dual of rec=", dann);
      #print("mac dual...", dann2);
   
      # Remove Reciprocals of Dual Elements with Monomials out of Range
      dualann:={};
      for s to nops(dann) do
         if type(dann[s], 'polynom') then
            dualann:=dualann union {dann[s]};
         fi;
      od;
      
      #dualann2:={};
      #for s to nops(dann2) do
       #  if type(dann2[s], 'polynom') then
        #    dualann2:=dualann2 union {dann2[s]};
       #  fi;
      #od;
      #print("dualann2", dualann2);
      
     fi;
 
#Auto-reduce
   reddualann:=auto_red(dualann);   
   t:=nops(reddualann);
   #reddualann2:=auto_red(dualann2);
    
  # Adding border monomials to Annihilator-----NOTE: auto-reducing could be done
   fullann:=dualann union b;    
   
  
#print("mac0"), mac0,
#print("mac"), mac,
#print("mour0"), mour0,
#print("mour11"), mour11,
#print("mour15"), mour15pol, 
#print("hankel ann"), hann;
#print("Ann via Dual=", fullann),
print("red mourrain dual=", reddualann, "#red dual=", t), 
#print("red mac dual mac=", reddualann2), 
#print("mourrai dual", dualann),
#print("mac dual", dualann2, dann2), 
print("red border=", b);
end:


#
# Macaulay' s 1916 algorithm to compute dual basis
#
#----------MODIFIED: New Argument deg added; Returns dual up to degree<=deg---------
#
macaulay0:= proc( f::list, var::list, z::list, deg, tol:=0 )
    local  mu, DD,t,ind, n,j,i, flag;
    n:= nops(var);
    DD:= [ ];
    i:=0;
    mu:=0;
    while true do
        t:= macaulay_step(f,var,z,i, tol,[], mu);
        #print(mu,nops(t), "step=",t);
        #--------Termination Cond Changes into stop at given degree deg 
        #(which will be deg of rec of gen function)---------
        #if mu=nops(t) then 
        if i=deg+1 then
            #print("Yes!", mu,nops(DD)- 1 );
            break;
        else
            DD:= [ op(t) ];
            mu:=nops(t);
            i:=i+1;
            #print("Mac. Mult. is now", mu );
        fi;
    od;
    #print("Mult:  = ", nops(DD) );
sort( DD, rlex_df );
end:

#
# Macaulay's 1916 Algorithm with MM11 improvement,
# Returns triangular basis
# Output is the primal-dual structure
#
#----------MODIFIED: New Argument deg added; Returns dual up to degree<=deg---------
#

macaulay:= proc( f::list, var::list, z::list, deg, tol:=0, upto:=infinity  )
    local  mu, BB, DD,t, t1, n,i, c ;
    n:= nops(var);
    DD:= [ ];
    BB:= [];
    i:=0;
    mu:=0;
    #while true and i<upto+1 do
    while true and i<deg+1 do
        t:= macaulay_step(f,var,z,i, tol, BB);
        #print(mu,nops(t), "step=",t);
        if 0=nops(t) then
            #print("Mult:  = ", nops(DD) );
            break;
        else
            t:= coefmatrix(t,var);
            t1:= cmaximal_minor( t[1], tol );#indices
            BB:= [ op(BB), op(t[2][t1]) ]; 

            # Orthogonalize current elements
            t[1]:= ReducedRowEchelonForm(
                Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));

            ## Update dual basis
            DD:= [ op(DD), op( matrix2diffs( t[1], t[2],var, tol) ) ];

            i:=i+1;
            #print("Mac. Added:", nops(t1) );
        fi;
    od;
    #print("Mult:  = ", nops(DD) );
DD,BB;
end:

#
#---------------------TO MODIFY Argument BB?---------------------------
#
mourrain_step := proc( f::list, var::list, z::list,DD::list,  tol:=0, BB:=[], opt := true, mm11 := true)
#mourrain_step := proc( f::list, var::list, z::list,DD::list,  BB, tol:=0, opt := true, mm11 := true)
local sd,un,c,t1,t2,tt1,tt2,p, k, row,R,rows,rr,n, M, NN, DIF, s, ro, i,j, RR, pp;
    n:= nops(var);
    sd:=nops(DD);
    #print(" mourrain_step_Input",DD);

    # Vector Lambda
    NN:= cand_set(  DD );
    #print("Cand_set:", ([to_polynomial(NN)]), nops(NN) );
#    print("Cand_set proj:", subs(d[2]=0,d[3]=0,to_polynomial(NN)) );

    #print("NN=", NN);
    s:=nops(NN);

###### Condition (i)
    ro:=0;# number of rows added
    M:=Matrix(nops(f),s);

    un:=[cat(a,1..s)];
    #cnt:=0;

    c:=first_comb(n,2); # For all combinations 1 \le k \le l \le n
    RR := NULL;
    while c <> NULL do
        #cnt:=cnt+1;

        tt1:= to_polynomial([seq(diff_df(DD[j], c[2]),j=1..sd)], var);
        tt2:= to_polynomial([seq(diff_df(DD[j], c[1]),j=1..sd)],var);
        #print( Matrix(<tt1>),Matrix(<tt2>) );
        #print("OK", s, d);
        p:=0;

        for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];
        od;

        #print("Const. (i) before:", collect(p,var));  # Print Constraints (i)

        if opt and p=0 then
            c:=next_comb(c,n);
            next;# no constraint here
        fi;

        # expand
        p := expand(p);
        #print(p);

        ### DISABLE This improvement reduces the constraints (i).
        ### In cond. (i) we can safely reduce the constraints wrt the
        ### previous primal/dual basis
        if opt and BB <> [] then
            p:= convert(
            [seq( BB[u]*coeffof(BB[u], p, var), u=1..nops(BB))],`+` );
            # optimized conditions!
            rows:= Array([lstcoefof(p,var)]);
        else #if BB <> []
            rows := NULL;
            for k to nops(BB) do
              rows:= rows, coeffof(BB[k], p, var);
            od:
            rows := Array([rows]);
        fi;

        #print("Const. (i) after :", collect(p,var));  # Print Constraints (i)
        #print("Closedness on ", DD, un, var ) ;
        #print("Closedness eqs:", closedness_equations(DD, un, var ) ) ;
        #print("Closedness:", lstcoefof(p,var) );
        #print("rows:", rows);
        # fi;

        #print(rows);
        #print("cond i: ", nops([lstcoefof(p,var)]) );
        R:=NULL;
        for row in rows do
            if row<>0 then 
                rr:= Array([seq(0,u=1..s)]); #lists don't work for big dimension
                for i to s do
                    rr[i]:= coeffof(un[i],row,un); ###
                od;
                R:=R, convert(rr,`list`);
            else 
                if not opt then
                    R:=R, [seq(0,u=1..s)];
                fi;
            fi; 
        od;

        if R<>NULL then
            M:= Matrix(<Matrix([R]), M> );
            ro:= ro + nops([R]);
            RR := RR, R;
            #print("M=",Matrix([R]));
        fi;

    c:=next_comb(c,n);

    od;#all combinations

#    print("Matrix:", Matrix([RR]) );


##### Condition (ii), nops(f) constraints
    DIF:= to_function(NN,var);
    for i to nops(f) do # f[i]
        for j to s do
            M[ro+i,j]:=
            eval( app_funct( DIF[j], f[i]) ,
            #eval( app_funct( DIF[j], f[i]) ,
                 [seq(var[k]=z[k],k=1..n)]);
        od;
    od;
    #print("Matrix:", M );

##### Condition (iii), MM2011
    # ADD CONDITION: DUALS OF BB MUST VANISH, nops(DD)-1 constaints
    R:=NULL;
    c:=NULL;
    if mm11 and BB <> [] then
        t1:= expand(add( un[k]*to_polynomial(NN[k],var), k=1..s));# current column span (Lmabda)
        #print(t1);

        for i from 2 to nops(BB) do # for all dual basis functions
            tt1:= coeffof(BB[i],t1,var);#coefficient of primal monomial in the column span
            tt2:= indets(tt1); # all lambda_{ik} twhich are multiplied by BB[i]

            #print(tt2, nops(tt2));
            # if the monomial BB[i] appears only in ONE corresponding lambda_{ik}
            
            ### DISABLE (always add constraint)
            #if false then
            if opt and nops(tt2)=1 then # If the BB[i] contributes only to a SINGLE column of the matrix
                for j to s do
                    #if un[j]=tt1 then
                    if un[j] in tt2 then
                        c:=c, j;
                        break;
                    fi;
                od;
            else
                rr:= Array([seq(0,u=1..s)]);
                for j to s do
                    rr[j]:= coeffof(un[j],tt1,un);
                od;
                R:=R,convert(rr,`list`);
            fi;
        od;

        #print("delete ",c);
        if R<>NULL then
            M := Matrix(<Matrix([R]), M> );
            #print("Condition III added", nops([R]),"rows" );
        fi;

        if c<>NULL then
            M:= DeleteColumn(M,[c]);
            NN:=subsop(seq([c][k]=NULL,k=1..nops([c])),NN);
            #print("Condition III removed",nops([c]),"cols" );
        fi;

        j := nops([R]);
        else # no condition iii
        j := 0;
    fi;

    #print("Columns:". to_polynomial(NN) );
    #print("Matrix:", M );
#    print("Int. Dimension:",Dimension(M));
    R:= nkernel( M, tol );
    #print(`Found`, nops(R). `vectors`);
    #print(`sol= `, R );

    if (nops(R)=0) or (BB=[] and nops(R)=nops(DD)-1) then
        print("Int. Method matrix size = ",Dimension(M),"Rows:", nops(f),"+",ro,"+", j, "Cols: ",s,"-",nops([c]) );
        #print("Int = ", M );
    fi:
   #print("Int. Method matrix size = ",Dimension(M),"Rows:", nops(f),"+",ro,"+", j, "Cols: ",s,"-",nops([c]) );

#### Computing new elements

    p:=NULL;
    for row in R do
        M:=Matrix(n+1,1);
        for i to nops(NN) do
#            if tol>0 then
                if tol=0 or abs(evalf(row[i]))>tol then
                    t1:= copy(NN[i]);
                    for j to Dimension(t1)[2] do
                        t1[n+1,j]:= t1[n+1,j]*row[i];
                    od;
                    M:=add_df(M,t1,tol);
                fi;
#            else
#                M:=add_df(M,t1,tol);
#            fi;
        od;
        p:= p, remove_zero(M, tol);
        #p:= p, M;
    od;

    if nops([p])> 0 then
        pp:= to_polynomial([p]);
#        print("New elements proj:", subs(d[2]=0,d[3]=0, pp) );
#        print("New elements deg:", map(degree,pp, d[1]), map(degree,pp, d[2]),map(degree,pp, d[3])  );
    fi:

    [p];
end:

kernelToDifferentials := proc(R::set, NN::list, n::integer, tol:=0)
local M, i, p, t1, row, j;
    
    p:=NULL;
    for row in R do
        M:=Matrix(n+1,1);
        for i to nops(NN) do
                if tol=0 or abs(evalf(row[i]))>tol then
                    t1:= copy(NN[i]);
                    for j to Dimension(t1)[2] do
                        t1[n+1,j]:= t1[n+1,j]*row[i];
                    od;
                    M:=add_df(M,t1,tol);
                fi;
        od;
        p:= p, remove_zero(M, tol);
        #p:= p, M;
    od;
[p];
end:

mourrain_matrix := proc( f::list, var::list, z::list,DD::list, tol:=0, BB:=[])
local sd,un,c,t1,t2,tt1,tt2,p, k, row,R,rows,rr,n, M, NN, DIF, s, ro, i,j;
    n:= nops(var);
    sd:=nops(DD);
    #print(" mourrain_step_Input",DD);

    # Vector Lambda
    NN:= cand_set(  DD );
    s:=nops(NN);

###### Condition (i)
    ro:=0;# number of rows added
    M:=Matrix(nops(f),s);

    un:=[cat(a,1..s)];
    c:=first_comb(n,2);
    while c <> NULL do
        t1:=[ seq(diff_df(DD[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(DD[j], c[1]),j=1..sd)];
        #print( t1,t2);
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        #print( Matrix(<tt1>),Matrix(<tt2>) );
        #print("OK", s, d);
        p:=0;
        for k to sd do
            p:= p + un[(c[1]-1)*sd + k] * tt1[k]
                  - un[(c[2]-1)*sd + k] * tt2[k];
        od;

        if p=0 then
            c:=next_comb(c,n);
            next;# no constraint here
        fi;

        # expand
        p := expand(p);
        #print(p);

        rows:= Array([lstcoefof(p,var)]);

        R:=NULL;
        for row in rows do
            #rr:= [seq(0,u=1..s)];
            rr:= Array([seq(0,u=1..s)]); #lists don't work for big dimension
            for i to s do
                rr[i]:= coeffof(un[i],row,un); ###
                #rr:=subsop(rr[i]=coeffof(cat(a,i),row,un),rr);
            od;
            #R:=R,rr;
            R:=R, convert(rr,`list`);
        od;

        if R<>NULL then
            M:= Matrix(<Matrix([R]), M> );
            ro:= ro + nops([R]);
            #print("M=",M);
        fi;
    c:=next_comb(c,n);
    od;#all combinations

##### Condition (ii), nops(f) constraints
    DIF:= to_function(NN,var);
    for i to nops(f) do # f[i]
        for j to s do
            M[ro+i,j]:=
            eval( app_funct( DIF[j], f[i]) ,
                 [seq(var[k]=z[k],k=1..n)]);
        od;
    od;

    print("Dimension:",Dimension(M));
    R:= nkernel( M, tol );
    #print(`Found`, nops(R). `vectors`);

#### Computing new elements

    p:=NULL;
    for row in R do
        M:=Matrix(n+1,1);
        for i to nops(NN) do
#            if tol>0 then
                if tol=0 or abs(evalf(row[i]))>tol then
                    t1:= copy(NN[i]);
                    for j to Dimension(t1)[2] do
                        t1[n+1,j]:= t1[n+1,j]*row[i];
                    od;
                    M:=add_df(M,t1,tol);
                fi;
#            else
#                M:=add_df(M,t1,tol);
#            fi;
        od;
        p:= p, remove_zero(M, tol);
        #p:= p, M;
    od;
    [p];
end:


mourrain_matrix_new := proc( f::list, var::list, z::list,DD::list, tol:=0, BB:=[], BBmon:=[],  opt := false)
local sss,sd,un,c,t1,t2,tt1,tt2,p, k, row,R,rows,rr,n, M, NN, DIF, s, ro, i,j;
    n:= nops(var);
    sd:=nops(DD);

    # Vector Lambda
    NN:= cand_set(  DD );
    #print("Cand_set:", ([to_polynomial(NN)]), nops(NN) );

    s:=nops(NN);

###### Condition (i)
    ro:=0;# number of rows added
    M:=Matrix(nops(f),s);

    un:=[cat(a,1..s)];
    #cnt:=0;

    c:=first_comb(n,2);
    while c <> NULL do
        #cnt:=cnt+1;

        t1:=[ seq(diff_df(DD[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(DD[j], c[1]),j=1..sd)];

        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        #print( Matrix(<tt1>),Matrix(<tt2>) );

        p:=0;
         for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];
        od;


        if opt and p=0 then
            c:=next_comb(c,n);
            next;# no constraint here
        fi;

        # expand
        p := expand(p);
        #print(p);
        #print("BBm", BBmon);

        # New alg
        if opt and BBmon <> [] then  # improved condition (i)

            p:= convert(
            [seq( BBmon[u]*coeffof(BBmon[u], p, var), u=1..nops(BBmon))],`+` );
            rows:= Array([lstcoefof(p,var)]);

            # Some Maple magic reduces the conditions according to the
            # previous dual space
            #sss := solve({lstcoefof(expand(add(_y[u]*BB[u] ,u=1..nops(BB)) - p),var)}, 
            #             {seq(_y[u],u=1..nops(BB))} );
            #rows:= Array(convert(map(rhs, sss), list));
            
        else
            #rows:= Array([lstcoefof(p,var)]);
            rows := NULL;
            for k to nops(BBmon) do
                rows:= rows, coeffof(BBmon[k], p, var);
            od:
            rows := Array([rows]);
        fi;
        #print(rows);

        R:=NULL;
        for row in rows do
            if row<> 0 then 
                rr:= Array([seq(0,u=1..s)]); #lists don't work for big dimension
                for i to s do
                    rr[i]:= coeffof(un[i],row,un); ###
                od;
                R:=R, convert(rr,`list`);
            else
                if not opt then
                    R:=R, [seq(0,u=1..s)];
                fi;
            fi; 
        od;

        if R<>NULL then
            M:= Matrix(<Matrix([R]), M> );
            ro:= ro + nops([R]);
        fi;
        c:=next_comb(c,n);
    od;#all combinations


##### Condition (ii), nops(f) constraints
    DIF:= to_function(NN,var);
    for i to nops(f) do # f[i]
        for j to s do
            M[ro+i,j]:=
            eval( app_funct( DIF[j], f[i]) ,
                 [seq(var[k]=z[k],k=1..n)]);
        od;
    od;

    #if (nops(R)=0) or (BB=[] and nops(R)=nops(DD)-1) then
    #print("NEW alg. mat. size = ",Dimension(M),"Rows:", nops(f), "+",ro, "Cols: ",s );
    #fi:

    #print("Matrix:", M );
#nkernel( M, tol );
M, NN;
end:

#
# Primal-Dual structure by Mourrain's 97 algorithm, with MM11 improvement
# Returns triangular basis
#
#----------MODIFIED: -------------------------
#New Argument deg added; Returns dual up to degree<=deg
#New Argument l added: need to compute bad mons not in recipe of \ell
#
#mourrain := proc( f::list, var::list, z::list, tol:=0, upto:=infinity, opt:= true, mm11:=true )
mourrain := proc( f::list, var::list, z::list, deg, l::table, tol:=0, opt:= true, mm11:=true )
local BB, DD,t,t1, n, c, badm;

    n:= nops(var);
    c:=1;
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    DD:= [ DD ];
    ####------------BB to be Changed into badmonomials???
    BB:= [1];
    badm:=[];
    #BB:=badmon(l,var);
    #####--------Termination Changed into upto=deg-------------------
    #while true and c<upto+1 do
    while true and c<deg+1 do

        t:= mourrain_step(f,var,z,DD, tol, BB, opt, mm11);
        ####-----ExampleL BB=[1,y,x*y,y^2] is (a subset of ) mon in the primal base; mourrain_step 
        ####  removes from its output mon 1,d2, d1d2, d2^2

        #print(mu,nops(t));
        #print("step=",t);
        if 0=nops(t) then
            #print("Mult:  = ", nops(DD) );
            break;
        else
            #print("deg=",c,"#D=",nops(t) );
            c:=c+1;

#            if not mm11 then
#                print("before :",nops(DD) ); 
#                print("now :",nops(t)); print(t);
#                firstNew := nops(t) - nops([DD]) - 1:
#                print("firstNew :",firstNew); 
#                t := t[firstNew..nops(t)];
#            fi:

            t:= coefmatrix(t,var);
            #print("coef_matrix:", t);
            t1:= cmaximal_minor( t[1], tol );#indices
            
            
            #print("max_minor=", t1 );
            #print("Update partial quotient basis");
            ## Update Partial quotient Basis
            if mm11 then
                ### ---- MODIFIED----
                ### in step/deg c, add bad monomials of degree c: badmon(l,var,c) to BB:
                BB:= [ op(BB), op(t[2][t1]) ]; 
                badm:=[op(badm), op(badmon(l,var,c))];
                BB:= [ op( {op(BB)} union {op(t[2][t1])} union {op(badm)}) ]; 
            else
                BB:= t[2][t1];
            fi;
            #print("basis:", BB);
            #print("bad mons", badm);
                

            #print("Orthogonalize current elements");
            # Orthogonalize current elements
           t[2]:= [op(t[2][t1]),op(subsop(seq( t1[j]=NULL,j=1..nops(t1)),t[2]))];
           ####------TO BE Modified?????
           t[1]:= ReducedRowEchelonForm(Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));
           #if t1<>[] then 
           #   t[1]:= ReducedRowEchelonForm(Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));
           #fi;
            #print("Update dual basis");
            ## Update dual basis
            if mm11 then
                DD:= [ op(DD), op( matrix2diffs( t[1], t[2],var, tol) ) ];
            else
                DD:=  matrix2diffs( t[1], t[2],var, tol);
            fi:

            #print("diffs: ", DD);

        fi;
    od;
    #print("Mult:  = ", nops(DD) );
DD, BB;
end:

#
# Primal-Dual structure by Mourrain's 97 algorithm, with MM11 improvement
# Returns triangular basis
#
#
#----------MODIFIED: New Argument deg added; Returns dual up to degree<=deg---------
#
#dualBasisNew := proc( f::list, var::list, z::list, tol:=0, upto:=infinity, opt := false )
dualBasisNew := proc( f::list, var::list, z::list, deg, tol:=0, opt := false )
local M, NN, BB, DD,t,t1, n, c, rc, v, vv, i, j, firstNew, k, BBmon, tt;

    n:= nops(var);
    c:=1;
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    #DD:= [ DD ];
    BB:= 1;

    BBmon:= [1];
    
    rc:= [];

    #####--------Termination Changed into upto=deg-------------------
    #while c<upto+1 do
    while c<deg+1 do
        
        # Integration method with (i,ii)
        M, NN := mourrain_matrix_new(f,var,z,[DD], tol, [BB], BBmon, opt);
        #print(mu,nops(t));
        #print("Matrix=",M);
        
        #print("del col:", subs(d[2]=0,d[3]=0,to_polynomial(NN)) );
        # Remove columns from matrix and column indexers
        M:= DeleteColumn(M, rc);
        NN:= subsop(seq( rc[j]=NULL,j=1..nops(rc)),NN);   

        #print("Matrix (rem)=",M);

        t := nkernel( M, tol );



        if 0=nops(t) then # are we done ?
            print("New alg. Matrix size at last step = ",Dimension(M) );
            print("Col Rem = ", M );
            print("Mult:  = ", nops([DD]) );
            print("overall columns removed = ", nops(rc) );
            break;
        else
            #print("deg=",c,"#D=",nops(t) );
            print("New alg. Matrix size = ",Dimension(M) );
            c:=c+1;
        fi;

        #print(t); #dz3 numeric bug
        #print(NN);

        # Grab new elements
        #nops(t) elements
        tt := kernelToDifferentials(t,NN,n,tol);
        DD:= DD, op(tt);

        # NOT needed - done with monomials BBmon anyway
        #if opt then        
        #    firstNew := nops([DD]) - nops(t) + 1:
        #
        #    for k from firstNew to nops([DD]) do
        #        BB := BB, to_polynomial(DD[k], var);
        #    od:
        #    #print("BB: ", BB);
        #fi:
        #print("diffs: ", DD);



        #print("kernel is :", tt);
        tt:= coefmatrix(tt,var);
        #print("coef matrix :", tt);
        v:= cmaximal_minor(tt[1], tol ):
        BBmon:= [ op(BBmon), op(tt[2][v]) ];
        #print(BBmon);



        t := kernelCoefMatrix(t);
        #print("kernel coef. matrix:", t);
        
        #print("cmax_", cmaximal_minor( t, tol ) );

        # Columns to remove in the next step
        v:= cmaximal_minor( t, tol ):
        vv:=0;
        for i to nops(v) do
            for j to nops(rc) do
                if rc[j] <= v[i]  then
                    v[i]:= v[i]+1;
                fi:
            od:
        od:
        rc := sort([ op(rc), op(v)]);
        #print("rc: ", rc );        

    od;
[DD];
end:


#
directionalMult2 := proc( f::list, var::list, z::list, ind::integer:= 1, tol:=0, upto:=infinity )
local M, NN, BB, DD,t,t1, n, c, rc, v, vv, i, j, np, a, ff, N, DIF,k,s,r,m;

    n:= nops(var);
    np := nops(f);
    c:=1;
    a:=Matrix(n+1,1);
    a[n+1,1]:=1;
    DD:= copy(a);
    #DD:= [ DD ];
    BB:= [1];
    ff:= copy(f);
    if ( upto < infinity ) then

            N:= op(ff);

        for i to upto do
            
            DD:= macaulay_step(ff, var, z, 1);# Jac
            print(i,"DD", DD);
            DIF:= to_function(DD,var);
            #
            for k to nops(DD) do
                if DD[k][1,1] = 1 then
                     for j to nops(ff) do
                        N:= N, diff_poly(ff[j],var,DD[k]);
                    od;
                fi:
            od;
            ff := [N];
            print("ff", nops(ff),ff );
        od:

    fi:
[N];
end:


#
directionalMult := proc( f::list, var::list, z::list, ind::integer:= 1, tol:=0, upto:=infinity )
local M, NN, BB, DD,t,t1, n, c, rc, v, vv, i, j, a, s, r, np, DIF, m;

    n:= nops(var);
    c:=1;
    a:=Matrix(n+1,1);
    a[n+1,1]:=1;
    DD:= copy(a);
    #DD:= [ DD ];
    BB:= [1];
    
    if ( upto < infinity ) then
    for i from 1 to upto do
        a[ind,1]:=i;
        DD:= DD, copy(a);
    od:
    fi:

    s := nops([DD]);

    print("Cols=",[DD], to_polynomial([DD]));

    r  := nops(f)*(upto);
    np := nops(f);

    M:=Matrix(r,s);
    

    DIF:= to_function([DD],var);
        for m from 0 to upto-1 do
    for i to np do # f[i]
            for j to s do
                M[np*m+i,j]:=
                eval( app_funct( DIF[j], subs(y=0,z=-1, expand( var[ind]^m*f[i]) ) ),
                      #eval( app_funct( DIF[j], f[i]) ,
                      [seq(var[k]=z[k],k=1..n)]);
            od;
        od:
    od;
    print("Matrix:", M );

    t := nkernel( M, tol );
    print("Mult:  = ", nops(t) );
    print("Ker :  = ", kernelToDifferentials(t,[DD],n,tol) );

return [DD];

#    while true and c<upto+1 do
        
        M, NN := mourrain_matrix(f,var,z,[DD], tol);# Integration method with (i,ii)
        #print(mu,nops(t));
        print("Matrix=",NN);
        print("Matrix=",M);
        
        t := nkernel( M, tol );

        if 0=nops(t) then # are we done ?
            #print("Mult:  = ", nops([DD]) );
            break;
        else
            #print("deg=",c,"#D=",nops(t) );
            #print("New alg. Matrix size = ",Dimension(M) );
            c:=c+1;
        fi;

        #print(t);
        #print(NN);

        # Grab new elements        
        DD:= DD, op(kernelToDifferentials(t,NN,n,tol));
        
        #print("diffs: ", DD);

        # t := kernelCoefMatrix(t);
        #print("kernel coef. matrix:", t);
        
        #print("cmax_", cmaximal_minor( t, tol ) );

#    od;
[DD];
end:


#
# Compute Hilbert Function
# input: a dual basis
#

hilbert_func := proc( BB::list )
local H, t, cd, c, e;

#print("hilbert_func_IN:", BB );
if (whattype(BB[1])=Matrix) then
    H:= NULL;
    cd := 0;
    c  := 0;
    for e in BB do
        t :=  degree( to_polynomial(e) );
        if t=cd then
            c:= c+1;
        else
            H:= H, c;
            cd:= cd+1;
            c:= 1;
        fi;
    od:
    # last value
    H:= H, c;
else
    H:= NULL;
    cd := 0;
    c  := 0;
    for e in BB do
        t :=  degree( e );
        if t=cd then
            c:= c+1;
        else
            H:= H, c;
            cd:= cd+1;
            c:= 1;
        fi;
    od:
    # last value
    H:= H, c;
fi;

[H];
end:


#
# Dual basis by classic Mourrain's '97 `Integration Method`
#
#----------MODIFIED: New Argument deg added; Returns dual up to degree<=deg---------
#
mourrain0 := proc( f::list, var::list, z::list, deg, tol:=0 )
local mu, DD,t, n,k ;

    n:= nops(var);
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    DD:= [ DD ];
    mu:=0;
    #####---------MODIFICATION: Changing the termination: do the loop deg times
    #while true do
    for k to deg do
        t := mourrain_matrix(f,var,z, DD, tol);
        #print(mu,nops(t));
        #print("step=",t);
        if mu=nops(t) then
            #print("Plain Integration:", Dimension(M) );
            #print("Yes!", mu,nops(DD)- 1 );
            break;
        else
            DD:= [DD[1],   op(t) ];
            print("DD:", DD);
            mu:=nops(t);
            #print("Int. Mult. is now:", mu + 1);
        fi;
        #cnt:=cnt+1;if cnt>3 then break; fi;
    od;
    #print("Mult:  = ", nops(DD) );
#sort(DD, cat(comp,_df) );
sort(DD, rlex_df );
end:

########################################################
####END-------------------Macaulay & Mourrain's Algorithms----------------
########################################################


##########################################################
##########################################################
### Elementary Operators on Differentials
##########################################################
##########################################################
#
# Graded lexicographic order
#
lex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
# df1 <lex df2 iff the upmost nonzero entry of df2 âÂ¢Â¬ÃÂ¬Ã¶âÃÂ¬â âÃÂ¬â  df1 is positive.
local n,i, df;
    df:= df2-df1;
    n:= Dimension(df1);

    if total_deg(df1) < total_deg(df2) then
        return true;
    fi;

    if total_deg(df1) = total_deg(df2) then
        for i from 1 to n-1 do
            if df[i]<>0 then
                if df[i] > 0 then
                    return true;
                else
                    return false;
                fi;
            fi;
        od;
    fi;
false;
end:
lex_df := proc ( ddf1::Matrix, ddf2::Matrix )
lex_c(leading_df(ddf1, lex_c), leading_df(ddf2, lex_c) );
end:

#
# Graded lexicographic order from the end
#
rlex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
# df1 <lex df2 iff the DOWNmost nonzero entry of df2 âÂ¢Â¬ÃÂ¬Ã¶âÃÂ¬â âÃÂ¬â  df1 is positive.
local n,i, df;
    df:= df2-df1;
    n:= Dimension(df1);


    if total_deg(df1) < total_deg(df2) then
        return true;
    fi;

    if total_deg(df1) = total_deg(df2) then
        for i from n-1 by -1 to 1 do
            if df[i]<>0 then
                if df[i] > 0 then
                    return true;
                else
                    return false;
                fi;
            fi;
        od;
    fi;
false;
end:
rlex_df := proc ( ddf1::Matrix, ddf2::Matrix )
rlex_c(leading_df(ddf1, rlex_c), leading_df(ddf2, rlex_c) );
end:
rlex_min := proc ( p , var::list)
Groebner:-TrailingTerm(p, grlex(op(var) ))[2] ;
end:

#
# Returns the total degree (order) of a differential
#
total_deg := proc(df1::Vector)
local s,i;
    s:=0:
    for i from 1 to Dimension(df1)-1 do
        s:=s+ df1[i];
    od;
    s;
end:

#
# Graded order, not used anymore here.
#
grlex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
local s1,s2,n,i, df;
    n:= Dimension(df1);

    s1:=0: s2:=0:
    for i from 1 to n-1 do
        s1:=s1+ df1[i];
        s2:=s2+ df2[i];
    od;
    if s1< s2 then
        return true;
    fi;

    # go to rlex
    if s1=s2 then
        return rlex_c(df1,df2);
    fi;
false;
end:
grlex_df := proc ( ddf1::Matrix, ddf2::Matrix )
grlex_c(leading_df(ddf1, grlex_c), leading_df(ddf2, grlex_c) );
end:

#
# leading term of differential wrt an ordering
#
leading_df:= proc( df::Matrix, compare:=rlex_c )
local t,lt,i,n,m;
    n,m:= Dimension(df);
    lt:= Column(df,1);

    for i from 2 to m do
        t:= Column(df,i);
        if not compare(t,lt) then
            lt:=t;
        fi;
    od;
lt;
end:

#
# Trailing term of differential wrt an ordering
#
trailing_df:= proc( df::Matrix, compare:=rlex_c )
local t,lt,i,n,m;
    n,m:= Dimension(df);
    lt:= Column(df,1);

    for i from 2 to m do
        t:= Column(df,i);
        if compare(t,lt) then
            lt:=t;
        fi;
    od;
lt;
end:

#
#Return the coeff. of p in variables var of the monomial m
#(from multires)
coeffof := proc(m,p,vvar)
local i,zs,lm,lc,k;
#    if m=0 then return 0;fi;
  lc := [coeffs(p,vvar,'lm')];
  lm := [lm];
  if member(m,lm,'k') then lc[k] else 0 fi;
end:

#
# Return the exponents of a monomial list
#
exp_of := proc(mm::list,var::list)
    local i,j, E , L;
    L:=NULL;
    for j to nops(mm) do
        E:=NULL;
        for i to nops(var) do
            E:= E, degree(mm[j],var[i]);
        od;
        L:= L,[E];
    od;
[L];
end:

#
# List coefficients of polynomial
#
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

#
#List the monomials of a polynomial p in the variables var:
#(from multires)
lstmonof := proc(p,var:=indets(PP))
local lm,r,c;
  lm := NULL;
  r := sort(p,var,tdeg);
  while r <> 0 do
     c := tcoeff(r,var,'m');
     lm := lm, m;
     r := expand(r-c*m);
  od;
    #ListTools:-MakeUnique([lm]);
op(sort([lm], proc (a, b) options operator, arrow;not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
#, descending
));
end:

#
#List the monomials of a polynomial system in the variables var:
#
lstmonsof := proc(PP::list,var:=indets(PP) )
local lm,p;
    lm := NULL;
    for p in PP do
        lm:= lm, lstmonof(p,var);
    od;
    ListTools:-MakeUnique([lm]);
#sort(%, proc (a, b) options operator, arrow; not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
sort(%, proc (a, b) options operator, arrow; not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
);
end:

#
# List monomials of a differential
# (not used)
lstterms := proc(df::Matrix )
    local t,n1,i,j,A;
    n1:= Dimension(df)[1];
    A:=NULL;
    #for df in DD do
        for j to Dimension(df)[2] do
            t:=Column(df,j);
            t[n1]:=1;
            A:= A, t;
        od;
    #od;
    #sort(ListTools:-MakeUnique([A]), cat(comp, _c) );
    #sort([A], cat(comp, _c) );
    sort([A], rlex_c );
end:

#
# Check for dublicates in a sorted list
# (not used)
check_list := proc ( l::list )
local i;

    for i to nops(l)-1 do
        if l[i]=l[i+1] then
            lprint(`Warning: Dublicates in the list`);
            return false;
        fi;
    od;
    true;
end:


#
# Return a differential as an operator (to be applied on a polynomial)
#
to_function := overload([
proc( db::Matrix,var::list) option overload;
local n,m;
    #print("to_function_IN:", to_polynomial(db));

    #n is number of variables-1, m number of terms
    n,m:= Dimension(db);

    unassign(`h`);
    unapply( add( db[n,k]* mul(1/factorial(db[i,k]), i=1..n-1) *
             diff(h(op(var)), [seq(var[i]$(db[i,k]), i=1..n-1)]) #diff
                  , k=1..m) #add
                  , h); #unapply
end,

proc( db::list,var::list) option overload;
local t, FF;

    FF:= [];
    for t in db do
        FF:= [op(FF), to_function(t,var) ];
    od;
    FF;
end
]);

#
# Apply Df on function t
#
app_funct := proc( Df, t )
Df( unapply(t) );
end:

#
# Return a differential as a polynomial
#
to_polynomial := overload([
proc( db::Matrix,
var::list :=[seq(d[i],i=1..(Dimension(db)[1]-1))]) option overload;
local t,j,n,m;

    #print("to_polynomial_input:",db,var , Dimension(db[1]));
    n:=nops(var);
    #m= number of terms
    m:= Dimension(db)[2];

    t:=0;
    for j to m do
       t:= t+  db[n+1,j]*mul( var[s]^db[s,j],s=1..n);
    od;
#print("to_polynomial_Output:",t);
t;
end,

proc( db::list,
var::list :=[seq(d[i],i=1..Dimension(db[1])[1]-1)] ) option overload;
local t, FF;

    FF:= NULL;
    for t in db do
        FF:= FF, to_polynomial(t,var);
    od;
    [FF];
end
]);

#
# Return a differential with one terms as a monomial
#
to_monomial := overload([

proc( db::Vector,
var :=[seq(d[i],i=1..(Dimension(db) -1))]) option overload;
local n;
    #print("to_monomial_input:",db,var , Dimension(db));
    n:=nops(var);
    #db[n+1]*
    mul( var[s]^db[s],s=1..n);
end,

proc( db::list,
var::list :=[seq(d[i],i=1..Dimension(db[1])[1]-1)] ) option overload;
local t, FF;

    #print( var);
    FF:= NULL;
    for t in db do
        FF:= FF, to_monomial(t,var);
    od;
    [FF];
end
]);

#
#  Input: coefficient matrix A, indexing diffs NN
#  Output: Differentials induced by A's rows
#
dmatrix2diffs := proc(R::Matrix, NN::list, tol:=0)
local n,p,M, j, i, t ,s ;

    #print("to_diffs_Input:", R, NN );
    n:=nops(NN[1]);
    s:=nops(NN);

    p:=NULL;
    for j to Dimension(R)[2] do
        #M:=NULL;
        M:=Matrix(n+1,1);
        for i to s do
            if abs(R[i,j])>tol then
                #print(i, NN[i], R[i,j]);
                t:= Matrix(<op(NN[i]),R[i,j]>);
                M:=add_df(M,t,tol);
            fi;
        od;
        p:= p, Matrix([M]);
    od;
    #print("to_diffs_Output:", p );
[p];
end:

#
# Create variable list [ x[1],...,x[n] ]
#
get_var := proc (n)
[seq(x[i],i=1..n)];
end:

##########################################################
### END---------------Elementary Operators on Differentials--------------------
##########################################################


###########################################################
###########################################################
###Operators on Differentials
###########################################################
###########################################################
# Makes Macaulay's matrix block of depth dp
# (not used)
#
macaulay_block := proc(f::list, var::list, z::list, dp::integer:=1 )
    local n, r, c, M, ci, mr, ri, i, t;

    n:= nops(var);
    if dp<0 then return [0]; fi;
    if dp=0 then return Matrix([0]); fi;

    r:= nops(f)*binomial(n+dp-2,dp-1);
    c:= binomial(n+dp-1,dp);
    M:= Matrix(r,c);

    r:=0: c:=0:
    ci:= first_mon( dp , n);
    while ci<>NULL do
        c:=c+1;
        mr:=0;
        ri:= first_mon(dp-1, n);
        while ri<>NULL do
            r:=r+1;
            for i to nops(f) do# f_i
                t:=diff_poly( mul(var[s]^ri[s],s=1..n)*f[i],
                              var, Matrix(<op(ci),1>) );
                M[mr + i,c]:=
                eval(t,[seq(var[s]=z[s],s=1..n)]);
            od;
            mr := mr+ i-1;
            ri:= next_mon( ri , dp-1);
        od;
        ci:= next_mon( ci , dp);
    od;
M;
end:

#
# `Integrate` a differential wrt i-th variable
#  (normalized)
#
int_df := proc( df::Matrix, i::integer)
local n,t, m, ci, j, k;

    #print("int_df_input:",df,"var",i);
    t:= copy(df);
    n:= Dimension(t)[1]-1;
    if i>n then
        lprint("Integration out of range");
        return df; fi;
    m:=Dimension(t)[2];

    for j to m do # Integrate
        t[i,j]:= t[i,j]+1;
    od;
    #print("int_df_output:",t);
t;
end:

#
# Remove terms with near-to-zero coefficient
# from a differential
#
remove_zero :=proc (df::Matrix, tol:=0 )
    local dd, n1,m,i,c ;
    #print("Remove zero IN:", df);

    dd:= copy(df);
    n1,m:= Dimension(dd);
    c:= NULL;

    for i to m do

        if abs(evalf(dd[n1,i]))<=tol then
            c:=c,i;
        fi;
#        if evalf(abs( Im(dd[n1,i])))<=tol then
#            dd[n1,i]:= Re(df[n1,i]);
#        fi;
#        if evalf(abs( Re(dd[n1,i])))<=tol then
#            dd[n1,i]:= Im(df[n1,i]);
#        fi;
    od;
    if nops([c])=0 then return dd; fi;
    if nops([c])=m then return Matrix(n1,1); fi;

DeleteColumn(dd,[c]);
end:

#
# Remove terms with EXACT zero coef
# from a differential
#
sremove_zero :=proc (df::Matrix )
    local dd, n1,m,i,c ;
    #print("Remove zero IN:", df);

    dd:= copy(df);
    n1,m:= Dimension(dd);
    c:= NULL;

    for i to m do

        if dd[n1,i]=0 then
            c:=c,i;
        fi;
#        if evalf(abs( Im(dd[n1,i])))<=tol then
#            dd[n1,i]:= Re(df[n1,i]);
#        fi;
#        if evalf(abs( Re(dd[n1,i])))<=tol then
#            dd[n1,i]:= Im(df[n1,i]);
#        fi;
    od;
    if nops([c])=0 then return dd; fi;
    if nops([c])=m then return Matrix(n1,1); fi;

DeleteColumn(dd,[c]);
end:


#
# Add two differentials, df1 + df2
#
add_df := proc (df1::Matrix, df2::Matrix, tol:=0)
    local ex, flag, t,n,i,j;
    #print(" add_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df1,Matrix(n+1,1)) then return copy(df2); fi;
    if Equal(df2,Matrix(n+1,1)) then return copy(df1); fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( t[ex,j],df2[ex,i] );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] + df2[n+1,i];
                if abs(evalf(t[n+1,j]))<=tol*.1 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([t,Column(df2,i)]);
            fi;
    od;
    #print(" add_df_Output",t);
#t;
remove_zero(t,tol); # zeros are not removed without this
end:

#
#  Add two differentials, df1 + df2 with symbolic coefficients
#
sadd_df := proc (df1::Matrix, df2::Matrix)
    local ex, flag, t,n,i,j;
    #print(" add_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df1,Matrix(n+1,1)) then return copy(df2); fi;
    if Equal(df2,Matrix(n+1,1)) then return copy(df1); fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( t[ex,j],df2[ex,i] );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] + df2[n+1,i];
                if abs(evalf(t[n+1,j]))=0 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([t,Column(df2,i)]);
            fi;
    od;
    #print(" add_df_Output",t);
t;
end:

#
# Add two differentials, df1 - df2
#
# BUG: sub_df(A,A);
sub_df := proc (df1::Matrix, df2::Matrix, tol:=0)
    local ex, flag, t,n,i,j;
    #print(" sub_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df2,Matrix(n+1,1)) then return df1; fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( i,j );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] - df2[n+1,i];
                if abs(t[n+1,j])<=tol*.1 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([Column(df2,i),t]);
                t[n+1,1]:= - t[n+1,1];
            fi;
    od;
    #print(" sub_df_Output",t);
t;
end:

#
# Multiply a differential by a scalar value
#
scalar_df := proc(df::Matrix, s )
    local n1,k, t;
    n1:= Dimension(df)[1];
    t:=df;
    for k to Dimension(df)[2] do
        t[n1,k]:= s * t[n1,k];
    od;
t;
end:

#
# Set coeff of dual(AA[i]) in DD[i] equal to 1
#
unify_coef := proc( DD::list, AA::list, var::list )
local Dp, res, i;
Dp:= to_polynomial(DD, var);

res:=NULL;
for i to nops(DD) do
    res:= res, scalar_df( DD[i], 1/coeffof(AA[i], Dp[i], var) );
od:

[res];
end:

#
# `Differentiate` a differential wrt variable i
#
diff_df := proc( df::Matrix, i::integer)
local n,t, m, ci, j, k;

#    print("diff_df_input:",df, to_polynomial(df), i);
    t:= copy(df);
    n:= Dimension(t)[1]-1;
    if i>n then
        lprint("Differentiation out of range");
        return df; fi;
    m:=Dimension(t)[2];

    # nullify terms of deg=0 wrt i
    ci:=NULL;
    for j to m do
        if t[i,j]=0 then
            ci:= ci, j;
        fi;
    od;#nullif
    t:=DeleteColumn(t,[ci]);
    m:=Dimension(t)[2];
    if m=0 then return Matrix(n+1,1); fi;

    for j to m do # Differentiate
        t[i,j]:= t[i,j]-1;
    od;
#    print("diff_df_output:",df,i);
t;
end:

#
# Check of the leading term of df appears as a term in LT.
# (not used)
has_term:= proc( df, LT::list)
    local d, i, m;
    #print("has_term_Input:", df, LT );
    d:= Dimension(df);

    for m to d[2] do
        for i in LT do
            if convert([seq(i[s]=df[s,m],s=1..(d[1]-1))], `and` )
            then
                return true; fi;
        od;
    od;
    #print("has_term_Output:", false);
    false;
end:

#
# Produce candidate set for the Integration Method
#
cand_set:= proc( DD::list )
local n, df, t, m, ci,i, j, k, L ;

    n:= Dimension(DD[1])[1]-1;
    #print(" cand_set In:", Matrix(<to_polynomial(DD)>));

    L:=NULL;

    for df in DD do
        for i to n do

            t:= copy(df);
            m:=Dimension(df)[2];
            #print(`next integration: `, d[i]);
            ci:=NULL;
            # for k from i+1 to n do # set i+1..n diffs to zero
            for k from 1 to i-1 do # set 1..i-1 diffs to zero
                for j to m do
                    if t[k,j]>0 then
                        ci:= ci, j;
                    fi;
                od;
            od;#set

            ci:=ListTools:-MakeUnique([ci]);
            if nops(ci)=m then
                t:=Matrix(n+1,1);
            else
                t:=DeleteColumn(t,ci);
            fi;

            L:= L, int_df(t,i);
            #II:= int_df(t,i);
            #if to_polynomial(II)<> 0 then L:= L, II; fi;
        od:
    od;
    #print(" cand_set In:", Matrix(<to_polynomial(DD)>),
    #      "Out:", Matrix(<to_polynomial([L])>));
[L];
end:

#
# Compute corank by SVD
#
ncorank := proc( M::Matrix, tol:=0)
    local r, i,m,n, Sv, K;
    #print("ncorank_input:", M );

    return min(Dimension(M))-LinearAlgebra:-Rank(M);

##########
    if tol=0 then # Exact computation
        return min(Dimension(M)) - Rank(M);
    fi;

    Sv:= SingularValues(evalf(M), output = [':-S'] );
    n,m:= Dimension(M);

    K:=0;
    for i to min(n,m) do

        if abs(Sv[i])<=tol then
            K:= K+1;
        fi;
    od;

    if min(n,m) < m then
        K:= K +  m - min(n,m)+1;
    fi;

    return min(n,m)-K;
end:


# PSEUDO-inverse..
#Ax=b
#x= A^-1 b


##
## Compute Matrix (pseudo-)inverse by SVD
##
m_inverse := proc(M::Matrix, tol:=1e-3)
    local m,n,U,Sv,Vt ;

    U,Sv,Vt:= SingularValues(evalf(M), output = [':-U',':-S',':-Vt'] );
    m,n := Dimension(M);
Transpose(Vt) .MatrixInverse(Matrix(Sv, shape=diagonal)[1..m,1..n]) . Transpose(U) ;
end:

##
## Compute Numerical Kernel using SVD
##
nkernel := proc(M::Matrix, tol:=0)
    local m,n,U,Sv,V,K,i,j;
    #print("nkernel_Input:", Dimension(M), tol );

    if tol=0 then # Exact computation
        return NullSpace(M);
    fi;

    U,Sv,V:= SingularValues(evalf(M), output = [':-U',':-S',':-Vt'] );
    V:= Transpose(V);
    n,m:= Dimension(M);

    #print("Singular values:", Sv);

    K:=NULL;
    for i to min(n,m) do

        if abs(Sv[i])<=tol then
            K:= K, V[..,i];
        fi;
    od;

    if min(n,m) < m then
        for i from min(n,m)+1 to m do
            K:= K, V[..,i]:
        od;
    fi;

    if nops([K])=0 then return {}; fi;
    #print("nkernel_Output:",nops([K]) );
{K};
end:

###########################################################
###END---------------------Operators on Differentials, etc.-------------------------
###########################################################


####################################################
####################################################
### Auxiliary functions
#######s#############################################
####################################################

#
# Computes the `Cyclic-n` polynmial system in variables x[1]..x[n]
#
cyclicn := proc( n )
local m,i,j, t, CN;

CN:=NULL;
m:=n-1;
for i from 0 to m-1 do # t=f_i
    t:=0;
    for j from 0 to m do # sum
        t:= t+ mul( x[(k mod n)+1], k= j..(i+j));
    od;
    CN:= CN, t;
od;
CN:= CN, 1-  mul( x[k], k=1..n);

[CN];
end:

#
# Computes a system with zero mult 2^n at x=0
#
expmultn := proc( n )
local S, i;

S:=NULL;
for i from 1 to n-1 do # t=f_i
    S:= S,  x[i]^3 + x[i]^2 - x[i+1];
od;
#S:=
[S, x[n]^2];
end:

#Benchmark system by Kobayashi et al.
kssn := proc( n )
local s;
lprint("Solution is", [seq(1,i=1..n)]);
s:=add(x[j],j=1..n) - n + 1;
[seq( x[i]^2 - 2*x[i]+ s, i=1..n)];
end:


#
# Next r-combination of [1..n] after c in lex-order
# nops(c)=r
#
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

#
# Lex-first r-combination of [1..n]
#
first_comb:= proc(n::integer,r::integer)
if r<=n then
   return [seq(1..r)];
else
    #print(`Warning: r>n combination requested`,r,n);
    return NULL;
fi;
end:

#
# RevLex-first degree r monomial in n variables
#
first_mon:= proc(r::integer,n::integer)
    return [r,seq(0,k=1..n-1)];
end:

#
# RevLex-Next degree r monomial in n variables after c
#
next_mon := proc( c::list, r::integer)
local nc,n,i,j;

    n:= nops(c);
    if c[n]=r then return NULL; fi; #finished
    nc:=c;

    i:=1;
    while c[i]=0 do
        i:=i+1;
    od;

    nc[i+1]:=nc[i+1]+1;
    #complete first non-zero element from the right with nc[i]-1
    if i=1 then
        nc[i]:=nc[i]-1;
    else
        nc[1]:=nc[i]-1;
        nc[i]:=0;
    fi;
    nc;
end:

####################################################
###End------------Auxiliary functions---------
#######s#############################################


########################################################
########################################################
#### Applications----
########################################################
########################################################

#
# Computes Normal form of p, given the primal-dual pair (BB,AA)
#
normal_form := proc ( p, var::list, z::list, BB::list, AA::list)
    local Sb, nf, i, m, dfs;
    m:=nops(BB);
    nf:=0;
    Sb:= seq(var[k]=z[k], k=1..nops(z));

    for i to m do
        nf:= nf +
        eval( app_funct( to_function( BB[i],var ) , p ), [Sb])
        * AA[i] ;
    od;
nf;
end:

#
# Computes the matrix of multiplication in R/Q_z
#
mult_table := proc ( f::list, var::list, z::list)
    local BB,AA, m, MM,j,i ;

    BB, AA := basis_pair(f,var,z);
    m:= nops(BB);
    MM:= Matrix(m);

    for i to m do
        for j to m do
            MM[i,j]:=
            normal_form( AA[i]*AA[j], var, z, BB,AA );
        od;
    od;
MM;
end:

#
# Computes the matrix of multiplication by a polynomial S in R/Q_z
#
mult_mat := proc (f::list, var::list, z::list, S)
local BB,AA, m, MM,j,i, NF ;
    
    BB, AA := basis_pair(f,var,z);
    m:= nops(BB);
    MM:= Matrix(m);
    
    
    for i to m do
        NF := normal_form( S*AA[i], var, z, BB,AA );
        for j to m do
            MM[i,j]:=
            coeffof( AA[j], NF, var );
        od;
    od;
    MM;
end:

#
# Return sign of number
#
sign_of  := proc (k)
if k=0 then return 0; fi;
sign(k);
end:

#
# Return the number of half-branches of real curve f=0 at point z
#
curve_branches := proc ( f::list, var::list, z::list )
    local n, Sb,m,i,MM,j,JJ, ff, BB, AA, ev, Phi;
    n:= nops(var);
    Sb:= [seq(var[k]=z[k],k=1..n)];
    ff:= [ op(f),
           Determinant(VectorCalculus:-Jacobian([op(f),add((var[k]-z[k])^2,k=1..n)] , var         ))];
    #print(`Map is ff= `, ff);
    BB, AA := basis_pair(ff,var,z );
    m:= nops(BB);

    #print(to_polynomial(BB) );

    JJ:= Determinant ( VectorCalculus:-Jacobian( ff , var ) );
    #print(`J= `, JJ);

    # find positive quad form
    for i to m do
        ev:= eval( app_funct( to_function( BB[i],var ), JJ ), Sb) ;
        if ev<>0 then
           if ev>0 then
               Phi:= BB[i];
           else
               print(`negative`);
           fi;
               break;
        fi;
    od;

    print(`Phi=`, to_polynomial(Phi) ) ;
    # Compute Matrix representation of quadratic form Phi
    Phi:= to_function(Phi,var);
    MM:= Matrix(m);
    for i to m do
        for j to m do
            MM[i,j]:=
            eval( app_funct( Phi ,
                             AA[i]*AA[j]
                             #normal_form( AA[i]*AA[j], var, z, BB,AA )
                           ), Sb );
        od;
    od;

    #print(MM);

    #Compute signature
    MM:=Eigenvalues( evalf(MM) );
    #print(`Eigenvalues=`, MM);
    2*add( sign_of(MM[i]), i=1..m );
end:

#
# Compute topological degree of mapping ff at point z
#
topological_degree := proc ( ff::list, var::list, z::list, tol:=0)
    local n, Sb,m,i,MM,j,JJ, BB, AA, ev, Phi;
    n:= nops(var);
    Sb:= [seq(var[k]=z[k],k=1..n)];

    BB, AA := basis_pair(ff,var,z, tol );
    m:= nops(BB);

    JJ:= Determinant ( VectorCalculus:-Jacobian( ff , var ) );

    # find positive quad form
    for i to m do
        ev:= eval( app_funct( to_function( BB[i],var ), JJ ), Sb) ;
        if abs(ev)> tol then
            Phi:= BB[i];
            break;
        fi;
    od;

    print(`got Phi=`, to_polynomial(Phi) ) ;
    # Compute Matrix representation of quadratic form Phi
    Phi:= to_function(Phi,var);
    MM:= Matrix(m);
    for i to m do
        for j to m do
            MM[i,j]:=
            eval( app_funct( Phi ,
                             #normal_form( AA[i]*AA[j], var, z, BB,AA)
                             AA[i]*AA[j]
                           ), Sb );
        od;
    od;

    #print(MM);
    #Compute signature and take absolute value
    Eigenvalues( evalf(MM) );
    abs( add( sign_of(MM[i]), i=1..m ) );
end:

#
# Create coefficient matrix of differentials BB
#
coefmatrix := proc (BB,v:=[] )
    local SBB,i,j,A,c,n,var;

    n:=Dimension(BB[1])[1]-1;
    if v=[] then
        var:=[seq(d[s],s=1..n)];
    else
        var:=v;
    fi;
    c:=to_polynomial( BB,var);
    #print("coefmat",c);
    SBB:= lstmonsof(c, var):
    A:= Matrix(nops(BB), nops(SBB) ) :
    for i to nops(c) do
        for j to nops(SBB) do
            A[i,j]:= coeffof(SBB[j],c[i], var ):
        od:
    od:
    [ A, SBB ] ;
end:

#
# Create coefficient matrix out of a set of kernel vectors
#
kernelCoefMatrix := proc (R::set)
Transpose( Matrix( convert(R,list) ) ):
end:


#
#  Input: coefficient matrix A, indexing polys SBB
#  Output: Polynomials induced by A's rows
#
matrix2polys:= proc ( A, SBB )
    local u,v,i,j,t,L;
    u,v := Dimension(A);

    L:=NULL;
    for i to u do
        t:=0;
        for j to v do
            t:= t + A[i,j]* SBB[j];
        od;
        L:=L, t;
    od;
[L];
end:

#
#  Input: coefficient matrix A, indexing polys SBB
#  Output: Differentials induced by A's rows
#
matrix2diffs:= proc ( A::Matrix, SBB::list, var::list, tol:=0 )
    local n,k,df,u,v,i,j,t,L;
    #print("matrix2diffs_IN:", A, SBB, var);
    u,v := Dimension(A);
    n:=nops(var);

    L:=NULL;
    t:=Matrix(n+1,1);
    for k to u do
        df:= Matrix(n+1,1);
        for i to v do
            if  tol=0 or abs(evalf(A[k,i])) > tol then
                t[n+1,1]:=A[k,i];
                for j to n do
                    t[j,1] := degree (SBB[i], var[j]);
                od;
                df:= add_df(df,t,tol);
            fi;
        od;
        L:=L, copy(df);
    od;
    #print("matrix2diffs_OUT:", L );
[L];
end:

#
# Compute a primal-dual orthogonal pair
#
basis_pair:= proc( f::list, var::list, z::list, tol:=0, upto:=infinity )
    local Db,A,i,C,ind;

    #for a suitable ordering (reverse to degree) we get already a good
    # basis
##    return mourrain(f,var,z, tol, upto);

    Db,A:= mourrain(f,var,z, tol, upto); # Get triangular basis


    C:= coefmatrix( Db, var );

    ind:=NULL;
    for i to nops(A) do
       ind:=ind, ListTools:-Search(A[i], C[2] ) ;
    od;
    ind:=[ind];

    # Orthogonalize basis
    #print("Got basis, eliminating upp. triang. part");
    C[1]:= ReducedRowEchelonForm(
        Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]));
    A:=C[2][ind];
    C[2]:=[op(A),op(subsop(seq( ind[j]=NULL,j=1..nops(ind)),C[2]))];

matrix2diffs( C[1], C[2],var, tol), A;
end:

#
# Given dual basis BB, find AA.  (under constuction)
#
make_basis_pair:= proc( BB::list, var::list)
    local Db,A,B,i,C,ind;

    C:= coefmatrix( BB, var );

    ind:=NULL;
    for i to nops(A) do
       ind:=ind, ListTools:-Search(A[i], C[2] ) ;
    od;
    ind:=[ind];

    #print(  Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]) );
    C[1]:= ReducedRowEchelonForm(
        Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]));
    A:=C[2][ind];
    C[2]:=[op(A),op(subsop(seq( ind[j]=NULL,j=1..nops(ind)),C[2]))];

    #print(C[2]);
    #print(C[1]);

#matrix2polys( ReducedRowEchelonForm(C[1]), subs(seq(var[k]=d[k],k=1..nops(var)), C[2])),
matrix2diffs( C[1], C[2],var, tol),
A;
end:

########################################################
#### END------------------Applications----
########################################################


############################################################
############################################################
###  Deflation, Root Isolation
############################################################
############################################################

#Krockener Delata
delta:= proc(i::integer, j::integer)
if i=j then return 1; else return 0; fi;
end:
#

##
## Deflation by perturbation of the system
##
deflate := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local n, AA, DD,N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    DD,AA:= basis_pair( expand(f),var,z,tol ) ; # compute dual basis
    #DD,AA:= mourrain( expand(f),var,z,tol ) ; # compute dual basis
    #print("Basis Pair:", to_polynomial(DD), AA ) ;
    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N:= new_system(  expand(f),var, z, per, DD, AA ); #make perturbed system

    J2:=VectorCalculus:-Jacobian( N[1], var ) ; # compute Jacobian
    J2:= subs(
        seq(N[2][i]=z[i],i=1..n),
        seq(N[2][i]=0,i=n+1..nops(N[2])  ), J2);

    #print(N[1]);
    #print(Matrix(<N[1]>),N[2]);
    #print(`J=`, J2 );
    #print(rmaximal_minor(J2), n );

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind + [seq(n,i=1..n)] ;
    else
        ind:= rmaximal_minor(J2,tol)+ [seq(n,i=1..n)]; # reduntant columns
    fi;
    print(`Rows:`,ind-[seq(n,i=1..n)]);
    #print(`Removing vars:`, N[2][ind] );
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );


    J1:= VectorCalculus:-Jacobian( N[1], N[2] );# compute augmented jacobian
    #print(J1);

    J1:= VectorCalculus:-Jacobian(
        subs(seq(N[2][ind[j]]=0,j=1..n), N[1]),
        subsop(seq( ind[j]=NULL,j=1..n),N[2]) );# compute jacobian

    #print(J1);
    print(`det`,evalf(
          subs( seq(N[2][i]=z[i],i=1..n),
                seq(N[2][i]=0,i=n+1..nops(N[2]) ),
                Determinant(J1)
              )));

subs(seq(N[2][ind[j]]=0,j=1..n), N[1]), subsop(seq( ind[j]=NULL,j=1..n),N[2]);
end:

##
## Deflation by LVZ/Zheng
deflate_lvz := proc( f::list, var::list, z::list, tol:=0 , v::symbol:=`a`)
local n, A, DD,N, J,Jev, rnum, vvars, i, R, rk ;
    n:=nops(var);

    unassign(v);
    vvars:= [seq(v[k],k=1..n)];
    rnum:= rand(1..100):

    J  :=VectorCalculus:-Jacobian( f, var ) ; # compute Jacobian
    Jev:= subs(seq(var[i]=z[i],i=1..n), J );
    rk := ncorank( Transpose(Jev) ); #default tolerance
    #print(Jev);

    A:= J . Matrix(<vvars>);
    A:= convert(A[..,1],list);

    R:=NULL;
    #print(rk);
    for i to rk do
        R:= R, ( Matrix([seq(rnum(),i=1..n)]) . Matrix(<vvars>) )[1,1];
    od;
    R:= [R];
    R[1]:= R[1] - 1;

[op(f),op(A), op(R) ], [op(var),op(vvars)];
end:


##
## Deflation by incremental dual computation
## (under construction)
deflate_incr := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local t, t1, i, n, BB, DD,N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(a, 1 .. nops(f))];

    # Compute D_1
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    BB:=[1];
    DD:= mourrain_step( expand(f),var,z,[DD], tol,BB ) ; # compute dual
    t:= coefmatrix(DD,var);
    t1:= cmaximal_minor( t[1], tol );
    BB:= t[2][t1] ; # corresponding primal

    print(`Computed:`, to_polynomial(DD), BB ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    for i to nops(DD) do
        print(to_polynomial(
            symbolic_dual(DD[i], cat(`a`,i) )
             ) );
    od;

DD;
end:

#
# Replaces coefficient of a dual element with variables ai
#
add_var := proc ( df::Matrix, aa:= `a` )
    local n,m,un,j,sd ;

    n,m:= Dimension(df);
    sd:= copy(df);
    for j to m do
        sd[n,j]:= sd[n,j]*aa;
        od;
sd;
end:

uadd_var := proc ( df::Matrix, aa:= `a` )
    local aav, n,q,un,j,sd ;

    n,q:= Dimension(df);
    sd:= copy(df);
    #sd:=unify_coef(sd,m,vars);
    aav:= [cat( aa, 1..q)];

    for j to q do
        sd[n,j]:= aav[j];
    od;
sd;
end:


#
# generic_dual
#
generic_dual := proc(dp::integer,n::integer,  aa:= `a` )
    local s,sd,c,rows,t1,t2,tt1,tt2,p,k, res,
    var, CC, SS, t, Ev, DD,un, i,j, lv;

    unassign(aa);
     var:= get_var(n);

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    DD:=[];
    SS:=NULL;

    for j to dp do

        # Base variable name for depth j
        lv:= aa; #cat(aa,j);

        # Get candidate set
        DD:= cand_set( [Ev, SS] ) ;

        # Add properly variables
        un:=[ seq(lv[k], k=1..nops(DD) )];
        t:= Matrix(n+1,1):
        for i to nops(DD) do
            DD[i]:= add_var(DD[i], un[i]);
            t:= sadd_df(t, DD[i]);
        od;
        SS:= SS, t;
    od;

    SS:= [Ev, SS] ;

   #### Compute Conditions (i)
    s := nops(DD);
    sd:= nops(SS)-1;

    c:=first_comb(n,2);
    rows:=NULL;
    while c <> NULL do
        t1:=[ seq(diff_df(SS[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(SS[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        p:=0;

        for k to sd do
            p:= p + un[(c[1]-1)*sd + k] * tt1[k]
            - un[(c[2]-1)*sd + k] * tt2[k];
        od;
        #print(lstcoefof(p,var) ) ;

        c:=next_comb(c,n);
    od;#all combinations

    #print("symbolic_dual_OUT:", SS);
[SS[-1], [lstcoefof(p,var)]] ;
end:

#
# symbolic_dual
#
symbolic_dual := proc(dp::integer,n::integer,  aa:= `a` )
    local s,sd,c,rows,t1,t2,tt1,tt2,p,k, res,
    var, SS, t, Ev, DD,un, i,j, lv ;

    unassign(aa);
    var:= get_var(n);

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    DD:=[];
    SS:=NULL;

    for j to dp do

        # Base variable name for depth j
        lv:=cat(aa,j);

        # Get candidate set
        DD:= cand_set( [Ev, SS] ) ;

        # Add properly variables
        un:=[ seq(lv[k], k=1..nops(DD) )];

        t:= Matrix(n+1,1):
        for i to nops(DD) do
            DD[i]:= add_var(DD[i], un[i]);
            t:= sadd_df(t, DD[i]);
        od;
        SS:= SS, t;
    od;

    SS:= [Ev, SS] ;

   #### Compute Conditions (i)
    s := nops(DD);
    sd:= nops(SS)-1;

    c:=first_comb(n,2);
    rows:=NULL;
    while c <> NULL do
        t1:=[ seq(diff_df(SS[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(SS[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        p:=0;

        for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];
        od;
        #print(lstcoefof(p,var) ) ;

        c:=next_comb(c,n);
    od;#all combinations

    #print("symbolic_dual_OUT:", SS);
[SS, [lstcoefof(p,var)]] ;
end:

#
# Generates order 1 constraints as polynomial equations
#
dual_constraints_1:= proc( f::list, var::list, z::list )
local n, un, c, M, C, p;

    n:=nops(var);
    un:=[cat(`a`,1..n)];

    c:=first_comb(n,2);
    M:=Matrix(nops(f),s);
    C:=NULL;
    while c <> NULL do
        p:= un[c[1]] - un[c[2]] ;
        C:= C, p;
        c:=next_comb(c,n);
    od;
    #for c in c2 do
    #    p:= un[c[1]] - un[c[2]] ;
    #    C:= C, p;
    #od;
[C];
end:

#
# Deflate by adding linear perturbation on the equations
#
deflate_lin := proc( f::list, var::list, z::list, tol:=0, my_ind:=[],DB:=[] )
local n ,N, J1,J2,DD, ind, per ;
    n:=nops(var);
    #per:=[cat(e, 1 .. nops(f))];

    #DD,AA:= basis_pair( expand(f),var,z,tol ) ; # compute dual basis
    if DB=[] then
        DD := mourrain  ( expand(f),var,z,tol )[1] ;
        else
        DD:= DB;
    fi;

    #print( to_polynomial(DD), AA ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N[1], var ) ; # compute Jacobian
    J2:= subs(
        seq(N[2][i]=z[i],i=1..n),
        seq(N[2][i]=0,i=n+1..nops(N[2])  ), J2);

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind + [seq(n,i=1..n)] ;
    else
        ind:= rmaximal_minor(J2, max(1e-6,tol) )+ [seq(n,i=1..n)];
    fi;
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    print(`Rows:`, ind -[seq(n,i=1..n)] );

    N:= new_system1(expand(f),var, DD); #make augmented system


subs(seq(N[2][ind[j]]=0,j=1..n), N[1]), subsop(seq( ind[j]=NULL,j=1..n),N[2]);
end:

#
# Deflate without adding any new variables
#
deflate_only := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local n, AA, DD,N, J1,J2, ind, per, w ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    DD,AA := basis_pair ( expand(f) ,var,z, tol ) ;
    #DD,AA := mourrain ( expand(f) ,var,z, tol ) ;
    print("Basis Pair:", to_polynomial(DD), AA ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N, w:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N, var ) ; # compute Jacobian
    J2:= subs(seq(var[i]=z[i],i=1..n) , J2);
    #print( N, nops(N) );
    #print( J2, Dimension(J2) );

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind;
    else
        ind:= rmaximal_minor(J2, tol); # full-minor columns
    fi;
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    print(`Rows:`, ind );

[ seq( N[ind[j]],j=1..n) ], var;
end:

#
# Input is system f, variables var, differentials DD, and list II of indices [i,j]
# Output is DD_i f_j for all indices [i,j] in II
# to be used together with deflation_hint
#
get_system:= proc ( fsys::list,var::list,DD::list, II::list )
    local ff, c;
   # print("get_system_IN", fsys,var,DD,II);

    ff:=NULL;
    for c in II do
            ff:= ff, diff_poly(fsys[ c[2]],var,DD[c[1]])  ;
    od;

   # print("get_system_OUT:", ff);
[ff];
end:


#
# Gives you a hine (the indices) of which diffs and equations provide
# a deflated system
#
deflate_hint := proc( f::list, var::list, z::list, DD::list, tol:=0 )
local n, AA, N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    #DD,AA := basis_pair ( expand(f) ,var,z, tol ) ;
    #DD,AA := mourrain ( expand(f) ,var,z, tol ) ;
    #print("Basis Pair:", to_polynomial(DD), AA ) ;

    #if nops(DD)=1 then
    #    lprint(`Warning: Simple root detected.`);
    #fi;

    N:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N, var ) ; # compute Jacobian
    J2:= subs(seq(var[i]=z[i],i=1..n) , J2);
    #print( N, nops(N) );
    #print( J2, Dimension(J2), tol );

    ind:= rmaximal_minor(J2, tol); # full-minor columns

    #print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    #print(`Rows:`, ind );

[seq( [ ind[k]-1 mod nops(DD)+1 , iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) ];
end:

#
# Maximum length of a rectangular domain
#
dom_size:= proc(dom::list)
    local t,s,i;

    s:=dom[1][2]-dom[1][1];
    for i from 2 to nops(dom) do
        t:=dom[i][2]-dom[i][1];
        if t>s then s:=t; fi;
    od;
s;
end:

#
# Center of a rectangular domain
#
dom_center:= proc(dom::list)
    [seq( (iend(dom[i])+istart(dom[i]))/2 , i=1..nops(dom) )];
end:


#
#
# Certify a multiple root of the approximate system f inside dom
#
certify_root := proc( f::list,var::list, dom::list )
    local tol, DF, n, z;

    n:=nops(dom);
    tol:= dom_size(dom);
    z := [seq( (dom[k][1]+dom[k][2])/2, k=1..n) ];

    print(`Certify tol:`,tol,`point:`,z   ) ;

    DF:= deflate ( f  , var , z , tol , []);
    #DF:= deflate_lin( f  , var , z , tol , []);

    print(`New system size:`,nops(DF[2]) ) ;

print(
    rump_test( DF[1], DF[2], i_box(dom, nops(DF[2]), tol) )
);
DF;
end:

rump_iter := proc( f::list,var::list, xs::list, XX::list, miter:=100)
    local E, es, i ;

    i:=1;
    E:= convert( rump_test( f,var,xs,XX ), list);
    es:=xs;
    while i<miter do
        i:=i+1;
        es:=dom_center(X_xs(E,xs));
        print("Next:", es );
        print(es,E);
        E:= convert( rump_test( f,var,es,E ), list);
    od;
X_xs(E,es);
end:

#
# Apply Rump's test for a simple root close to xs in a given range XX
#
rump_test :=proc ( f::list,var::list, xs::list, XX::list )

local i,E;
    E:= rump(f,var,xs,XX);#
    print(`Inclusion:`, E );
    print(xs,XX);

    for i to nops(var) do
        if not inclusion(E[i,1],XX[i]) then
            print(`At position`,i,`:`, evalr(E[i,1]+xs[i]),evalr(XX[i]+xs[i]) );
            RETURN(false);
        fi;
        #E[i,1]:= evalr(E[i,1]+xs[i]);
    od:
print(`Inclusion made.`);
E;
end:

#
# Compute Rump's inclusion formula
#
rump := proc ( f::list,var::list, xs::list, X::list)
local Id, J, R, M, fev;

J:= VectorCalculus:-Jacobian(f, var);
Id:= Matrix(nops(var),shape=identity) ;

#Jacobian evaluated on X+xs
M:= eval_on_ints( var, X_xs(X,xs), J ) ;

#print(`M=`,M);
#print(f,var, J);
#print( subs( seq( var[j]=xs[j],j=1..nops(var)),J )  ) ;

    print(`det`,
          #subs( seq( var[j]=xs[j],j=1..nops(var)),J ),
      ` = `,
          Determinant(subs( seq( var[j]=xs[j],j=1..nops(var)),J )) ) ;

# Inverse of Jacobian evaluated on initial approximation

#print(`J=`, J);
#print( subs( seq( var[j]=xs[j],j=1..nops(var)),J ) ) ;
#print( Determinant(subs( seq( var[j]=xs[j],j=1..nops(var)),J )) ) ;

R:= MatrixInverse(
    subs( seq( var[j]=xs[j],j=1..nops(var)),J )  ) ;

# Evaluation of f over xs

fev:= Transpose(Matrix( subs(seq(var[j]=xs[j],j=1..nops(var)), f )  )) ;
#print(`f_ev =`, fev);
#print(`R.M =`, mat_prod(R,M));

# Rump's Formula: -R.fev + (Id-R.M).X
mat_add( -R.fev , mat_prod(  mat_sub(Id,mat_prod(R,M)),
               Transpose(Matrix(X)))  ) ;
end:


#mult := proc (f,var,z, tol:=0, comp:=rlex)
#nops( get_dbasis(f,var,z,tol,rlex) );
#end:

#
# Sets coeff of primal monomial to 1
# (not used)
#
refine_basis:=  proc(A::list, dual_basis::list, var::list )
    local RB,i,j, n,m,c,k;
    n:= nops(var);
    RB:=dual_basis;
    for i to nops(A) do
        j:=1;
        while j<= Dimension(RB[i])[2] do

            if Column(RB[i],j)[1..n]=A[i][1..n] then
                RB[i]:= scalar_df( RB[i], 1/RB[i][n+1,j] ) ;
                #break;
            fi;

            for k to i-1 do
                if Column(RB[i],j)[1..n]=A[k][1..n] then
                    RB[i]:= sub_df( RB[i],scalar_df(RB[k],RB[i][n+1,j]));
                fi;
            od;
            j:=j+1;
        od;
    od;
RB;
end:

#
# Given a monomial/list of monomials in var, computes the dual element(s).
# (not used)
#
dual_monomial := overload([

proc(var::list, A::list) option overload;
    local n,i,j,t,Dset;
    n:=nops(var);

    Dset:=NULL;
    for i from 1 to nops(A) do
        t:=Matrix(n+1,1);
        t[n+1]:=1;

        for j from 1 to nops(var) do
            t[j,1] := degree (A[i], var[j]);
        od;
        #print( A[i], t );
        Dset:= Dset, t;
    od;
[Dset];
end,

proc(var::list, A) option overload;
    local n,j,t;
    n:=nops(var);

    t:=Matrix(n+1,1);
    t[n+1]:=1;

    for j from 1 to nops(var) do
        t[j,1] := degree (A, var[j]);
    od;
t;
end
]);
#
# Replaces coefficient of a dual element with variables ai
#
symb_diff := proc ( df::Matrix, aa:= `a` )
    local n,m,un,j,sd ;

    n,m:= Dimension(df);
    un:=[cat(aa,1..m)];

    sd:= copy(df);
    for j to m do
        sd[n,j]:= un[j];
        od;
sd;
end:

#
# Perturbe wrt a quotient basis
#
new_system:= proc ( f::list, var::list, z::list, per::list, dual_basis::list, pr_basis)
    local pp,all, n,g,i,j,ff,t, fu;
    all:=op(var);
    n:=nops(var);

    pp,all:= pert_system( f,z, var, per , pr_basis ) ;

    ff:=NULL;
        for j to nops(f) do
    for i to nops(dual_basis) do
            ff:= ff, diff_poly(pp[j],var,dual_basis[i])  ;
        od;
    od;

[ff],all;
end:

#
# apply linear perturbation e[j,i] on equations
#
new_system1:= proc ( f::list, var::list, dual_basis::list, AA::list )
    local pp,all, n,g,i,j,ff,t, fu;
    all:=op(var);
    n:=nops(var);
    t:=nops(f);
    ff:=NULL;

    for j to t do
        #ff:= ff, f[j];
        for i from 1 to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i]) + e[j,i];
            #subs(seq(var[j]=var[j]-z[j],j=1..nops(z)), AA[j]) * e[j,i]  ;
            all:=all , e[j,i];
        od;
    od;
    ff:=[ff];
    #print(`New system is:`, Matrix(<ff>) );

ff,[all];
end:



#
# Just add equations, not variables
#
new_system2:= proc ( f::list,var::list,dual_basis::list )
    local i,j,ff ;

    ff:=NULL;
    for j to nops(f) do
        for i to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i])  ;
        od;
    od;

[ff],var;
end:

#
# Make system with dual coefficients as variables
# DD must have symbolic coefficients, BB it's dual monomial basis
#
deflate_system:= proc ( f::list,var::list, z::list, tol:= 0, ch:=[], iv:= {} )
    local i,j,ff , B, A, H, P, nvar, avar, v, p, J2, ind;

    # Compute primal-dual pair
    B, A := mourrain( f, var, z , tol);
    print("Pair: ", B, A );

    # extract hilbert function
    #H    := hilbert_func( B );
    # compute parametric dual
    P    := parametric_basis( A, B,  nops(var) ) ;
    print("Parametrized dual: ", P );

    nvar:= convert(indets(P),list);
    avar:= [op(var),op(nvar)];

    # Apply parametric dual elements to f
    ff:=NULL;
    for j to nops(f) do
        for i to nops(P) do
            ff:= ff, diff_poly(f[j],var, P[i])  ;
        od;
    od;
    ff:= simplify([ff]);
    print(ff, avar );

    # Get approximate values of the parameters
    B:= subs( seq(var[i]=z[i],i=1..nops(var) ) , ff );
    H:= NULL;
    for p in B do
        if nops(indets(p) )>0 then H := H, p; fi;
    od;
    H:= [H] ;
    v:= solve( H , convert(nvar,set) );
    print("System : ", H );
    if iv<>{} then v:= iv; fi;

    print("Initial point: ", v);


    # Approximate root of the deflated system
    p:= [op(z), op(subs( v, nvar))];

    J2:=VectorCalculus:-Jacobian( ff, avar ) ; # compute Jacobian
    J2:= subs(seq(avar[i]=p[i],i=1..nops(p)) , J2);
    print("J=", J2);

    ind:= rmaximal_minor(J2, tol); # full-minor columns
    if ch<>[] then ind:= ch; fi;

    print(`Rows:`, ind );

    [ seq( ff[ind[j]],j=1..nops(ind)) ], avar, p;
#ff;
end:


#
# Compute the dual basis given the primal basis A incrementally
# Oslo2012
parametric_basis := proc( AA::list, BB::list, n::integer, aa:= `a` )
local s,sd,c,rows,t1,t2,tt1,tt2,p,k, res, NZ,
    var, SS, t, Ev, Dl,un, i,j, lv, m, r, H, u , Dl0, v, free, R, CC, CCs;
    CCs:= NULL;

    H:= hilbert_func( BB );

    unassign(aa);
    var:= get_var(n);

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    Dl:=[];
    SS:= NULL;

    j:=1;
    for u from 2 to nops(H) do

        ## Get candidate set for degree u-1
        Dl0:= cand_set( [Ev,  SS ] );

        for v to H[u] do

            #j := add(H[k],k=1..u-1) + v ; # element counter
            j := j+1;
            #print("--------------------- Element #", j, " deg=", u-1, "-------------------------");

            if  Dimension(BB[j])[2]=1 then
                t1:= BB[j];
                t1[n+1,1]:= 1;
                SS:= SS, t1;
                print("got: ", to_polynomial(t1)) ;
                next;
            fi;

            # Base parameter name for functional j
            lv:=cat(aa,j);

            ## Candidate set for element j
            Dl:= NULL;
            for k to nops(Dl0) do
                Dl := Dl, copy(Dl0[k]);
            od:
            Dl:= [Dl];

            #print('cand_set_is', Dl , un);

            ## Adding variables for dual element j to all candidates
            un:=[ seq(lv[k], k=1..nops(Dl) )];
            free:= NULL;
            t:= Matrix(n+1,1):
            for i to nops(Dl) do
                r,m:= Dimension(Dl[i]);

                # "free" variables
                if to_polynomial(Dl[i])=0 then
                    un[i]:=w[i];
                    free:= free, w[i];
                fi;

                for k to m do
                    Dl[i][r,k]:= Dl[i][r,k]*un[i];
                od;
                t:= sadd_df(t, Dl[i]);
                #fi;
            od;

            ###### Condition (i)
            #
            #print('cand_set_is', Dl , un);
            #print("Parameters:", un);

            ##  Employ condition (iii) : eliminate variables+add conditions

            R:=NULL;
            NZ:=NULL;
            c:=NULL;

            #print( Dl ) ;
            t1:= expand(add( to_polynomial(Dl[k],var), k=1..nops(Dl) ));
            #print('t1', t1, j);

            #for i from 2 to nops(AA) do
            #for i from 2 to j-v do
            for i from 2 to add(H[k],k=1..u) do
                tt1:= coeffof(AA[i],t1,var);
                tt2:= indets(tt1);

                if nops(tt2)=1 then # get nb of vars/terms of tt1
                    for k to nops(Dl) do
                        if un[k] in tt2 then   # for vv in un intersect tt2 do
                            Dl:=subs(un[k]= delta(i,j) , Dl);
                            t:=subs(un[k]= delta(i,j), t);
                            #print(un[k], "= ", delta(i,j) );
                            un[k] := delta(i,j);
                        fi;
                    od;
                else
                    if nops(tt2) > 0 then
                        # keep condition tt1
                        R:= R, tt1;
                        print('Condition', tt1 );
                    fi;
                fi;
            od; # end i

            ##############
            ##############
            t1:= to_polynomial( BB[j], var);
            t1:= [lstmonof( t1, var)];
            for i to Dimension(t)[2] do
                t2:= mul( var[s]^t[s,i],s=1..n);
                if  not member( t2, t1) then
                    if nops(t[n+1,i])=1 and not is(t[n+1,i],constant) then
                        #print( t[n+1,i], " = ", 0 );
                        un:= subs( t[n+1,i]=0, un);
                        R:= op( subs(t[n+1,i]=0, [R]) );

                        t:= subs( t[n+1,i]=0, t);
                    else
                        R:= R, coeffof(t2, to_polynomial(t,var),var);
                    fi;
                else
                    if nops(t[n+1,i])=1 and not is(t[n+1,i],constant) then
                        NZ:= NZ, t[n+1,i]<>0;
                    fi;
                fi;
            od;


            #print('cand_set_is', to_polynomial(Dl) );
            #print("Reduced parameters:", un, R);
            #print("t=", t );

            t := sremove_zero ( t );
            SS:=  SS, t;


if j-v-1>0 then

    #print(v, "SS ", SS, 1..j-v ) ;
    #print("Closedness on ", [Ev, SS[1..j-v-1]], un, var ) ;
    CC:= [ op(closedness_equations([Ev, SS[1..j-v-1] ], un, var, AA  )), R ];

    #print("NZ: " , NZ) ;

    free:= {free};
    #print("free parameters:", free);
    CC:= eliminate(CC,free)[2];
    #print("Closedness: " , CC) ;

# return conditions instead of solving
#if false then

    CCs:= solve(CC);
    print("values: ",CCs );
    if ( nops([CCs]) > 1 ) then
        print("TROUBLE, found ", nops([CCs]), "solutions :");
        print("Retry with constraints");
        CCs:= solve( [op(CC), NZ] ) ;
        print("new values: ",CCs);
        SS:= op(subs(CCs, [SS])) ;
    else
        if ( nops([CCs]) =0 ) then
            print("TROUBLE, found NO solutions :");
            print("Retry with constraints");
            CCs:= solve( [op(CC), NZ] ) ;
            print("new values: ",CCs);
            SS:= op(subs(CCs, [SS])) ;
        else
            SS:= op(subs(CCs, [SS])) ;
        fi;
    fi;
#fi;
fi;
            #if j=2 then print("got: ", to_polynomial(SS));
            #else
            #print("got: ", to_polynomial( SS[j-1]  )) ; #fi;

        od; # end u ###########################

        #print("====================   degree= ", u-1, " ==> recovered: ", to_polynomial(SS[j-H[u]..j-1]) , "=======================") ;
    od;# end v

SS:= [Ev,SS];
for k to nops(SS) do
    SS[k]:= sremove_zero (SS[k]);
od:
SS;
#SS,CC;
end:



closedness_equations := proc( SS::list, un::list, var::list, BB:= [] )
local p, n, t1, t2, tt1, tt2, c, res, sd, k;

    n:= nops(var);
    sd:= nops(SS);
    c:=first_comb(n,2);
    res:=NULL;

    #print("n=",n, "sd=", sd , "#un", nops(un) , SS ) ;

    while c <> NULL do
        t1:=[ seq(diff_df(SS[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(SS[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);

        p:=0;
        for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];

        od;

        if BB <> [] then  # improved condition (i)
            p:= convert(
                [seq( BB[u]*coeffof(BB[u],expand(p),var), u=1..nops(BB))],`+` )
        fi;

        #print("ind= ", c , "p= ", p ) ;

        res:= res, lstcoefof(p,var) ;
        c:=next_comb(c,n);
    od;#all combinations

#print("p=", p ) ;

[res];
end:

#
# Modified Newton's Method
#
# f: system, var: variales, z: approximation
# tol: requested accuracy, eps: error bound on z,
# ITER:  max iterations
#
newton_mod := proc( f::list, var::list,z::list, tol:= 0.001, eps:= 0.01, ITER:=100)
    local Dx, ZZ, c, DD, ind, S;
    c:=0;
    Dx:= 2*tol;
    ZZ:=z;

    DD := basis_pair ( expand(f) ,var,ZZ, eps )[1] ;
    #DD := mourrain   ( expand(f) ,var,ZZ, eps )[1] ; #Initial basis

    ind := deflate_hint(f,var,ZZ, DD, eps); #Computed once?
    S:= get_system(f,var,DD,ind); # deflated system
    print("Basis:", to_polynomial(DD) );
    print("System:", S , "Solution :", solve(S,var) );

    # Newton-Raphson Method, modified
    while evalf(max(map(abs,Dx)))>tol do
        print("------------- it", c,"----------------------");

        Dx := newton_next(S,var,ZZ,tol);
        #print(Dx);
        ZZ := ZZ - Dx;
        print("Next:", ZZ);
        c:=c+1;
        if c>ITER then
            lprint(ITER,`newton mod: iterations reached.`);
            break;
        fi;

        # Update system
        DD := basis_pair ( expand(f) ,var,ZZ, eps )[1] ;
        #DD := mourrain  ( expand(f) ,var,ZZ, eps )[1] ;# Refine basis
        ind := deflate_hint(f,var,ZZ, DD, eps); #Computed again ...
        S  := get_system(f,var,DD,ind); # Refine system
        print("Next basis:", to_polynomial(DD) );
        print("Next System:", S , seq(D[ind[i][1]]*P[ind[i][2]],i=1..nops(S)) );
        print("S solution :", solve(S,var) );

    od;

    lprint(`newton_mod: iterations:`,c);
    ZZ;
end:

#
# Newton's Method
#
newton := proc( f::list, var::list,z::list, tol:= 0.0001, ITER:=500)
    local Dx , ZZ, c;
    c:=0;
    Dx:= 2*tol;
    ZZ:=z;
    while evalf(max(map(abs,Dx)))>tol do
        Dx := newton_next(f,var,ZZ,tol);
        #print(Dx);
        ZZ := ZZ - Dx;
        print("Next:", ZZ, evalf(max(map(abs,Dx))) );
        c:=c+1;
        if c>ITER then
            lprint(ITER,`newton: iterations reached.`);
            break;
        fi;
    od;
lprint(`newton: iterations:`,c);
ZZ;
end:

#
# Newton Operator
#
newton_step := proc( f::list, var::list,z::list, tol:= 0.001)
z - newton_next( f, var, z, tol);
end:

#
# Newton next update
#
newton_next := proc( f::list, var::list,z::list, tol:= 0.001)
local Ji, fx;

    Ji:= m_inverse( # (pseudo-)inverse of Jacobian
        subs( seq(var[i]=z[i],i=1..nops(var)),
              VectorCalculus:-Jacobian(f,var)
            ));
    fx:= Matrix( < subs(seq(var[i]=z[i],i=1..nops(z)), f )>) ;

convert( Ji . fx , list);
end:

#
#Compute perturbed polynomial system  wrt the elements of A
#
pert_system:= proc( f::list, z::list, var::list,per::list, A::list)
local pp, i, j, all;
    all:=op(var);
    pp:=NULL;
    for i to nops(f) do
            pp:= pp, expand( pert_poly(f[i],z,var,A,per[i])) ;
        for j to nops(A) do
        all:= all, per[i][j];
        od;
    od:
[pp],[all];
end:

#
#Compute perturbed point
#
pert_point:= proc( z::list , e:= 0.005, d::posint:= 2 )
local pp;
if e=0.0 then return z; fi;
pp:= RandomTools[Generate]( list( float(range=e..3*e, digits=d), nops(z) ) );
pp:= pp - [seq(2*e,i=1..nops(z)) ] ;
z+pp;
end:


#
# Perturb polynomial wrt the elements of A
#
pert_poly := proc (p, z::list, var::list, A::list, k )
local n,i, g;
    #print("pert_poly input", p, z );
    n:=nops(var);
    g:=p;
# add new variables
    for i to  nops(A) do
        #g:= g+ subs(seq(var[j]=var[j],j=1..nops(z)), A[i])* k[i];
        g:= g+ subs(seq(var[j]=var[j]-z[j],j=1..nops(z)), A[i])* k[i];
    od;
    #print("pert_poly output", g );
expand(g);
end:

#
# Add noise to coefficients of a polynomial system
#
add_noise := proc ( f::list, ns:=1e-3 )
local Pt,m,i, g, j;
    g:=f;
    for i to  nops(f) do
        #random numbers
        Pt:=Array(RandomTools:-Generate(
            list(float(range=-0..ns,'method=uniform'),nops(f[i]))),
                  'datatype=float[8]');
        j:=1;

        for m in f[i] do # perturbe f_i
            g[i]:= g[i] +  Pt[j]* m ;
            j:=j+1;
        od;
    od;
g;
end:

#
# Differentiate polynomial  (normalized)
#
diff_poly := proc (p, var::list, df::Matrix   )
 local s,j,i,n, g, res;
    #print("diff_poly_input: ", p, var, df);
    n:=nops(var);
    s:= Dimension(df)[2];

    res:=0;
    for j to s do
        g:=p;
    for i to n do # normalized differentiation
            g:= diff( g, [ var[n-i+1]$df[n-i+1,j] ]) / df[n-i+1,j]! ;
        od;
        res:=res + df[n+1,j]*g; #coeff times g
    od;
res;
end:

#
# Apply (normalized) functionals on system f
#
diff_system := proc ( f::list,var::list,dual_basis::list )
    local i,j,ff ;

    ff:=NULL;
    for j to nops(f) do
        for i to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i])  ;
        od;
    od;

[ff];
end:

#
# Return the indices of n independent rows of an mxn Matrix
#
rmaximal_minor:= proc( M::Matrix, tol:=0.05)
#print("rmax", M);
cmaximal_minor(Transpose(M), tol );
end:

#
# Returns the indices of n independent columns of an nxm Matrix
#
cmaximal_minor:= proc( M::Matrix, tol:=0)
local RR, i,j,n,m, cc;
    #print("cmaximal_minor_IN:", M );

    RR:= QRDecomposition( M , output = ['R'], fullspan=false);
    RR:= ReducedRowEchelonForm(RR) ;
    #print("max_minor: R=", RR, "rank=", Rank(RR), ncorank(RR));
    #print("QR - rank: ", QRDecomposition(M, output = ['R','rank']));
    #print("redrow: ", RR);

    n, m:= Dimension(RR);

    #Find principal elements in RR-matrix
    cc:=NULL;
    i:=1;
    j:=1;
    while i<=n and j<=m do
        #print("(",i,j,"): ", abs(RR[i,j]), ">", tol );
        if(abs(evalf(RR[i,j]))) > tol then #Caution for errors here!
            cc:= cc, j;
            i:=i+1;
            #else
            #    print( "reject = ", tol );# reject
        fi;
        j:=j+1;
    od;
    #print("cmaximal_minor_out:", cc );
    return [cc];
end:


##############################
# Rump's Test help functions
##############################

# Matrix Multiplication with evalr
mat_prod := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if m1<>n2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m2);
    for i to n1 do
        for j to m2 do
            for k to n2 do
                P[i,j]:= evalr(P[i,j] + evalr(A[i,k]*B[k,j]));
            od;
        od;
    od;
P;
end:

# Matrix Addition with evalr
mat_add := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if n1<>n2 or m1<>m2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m1);
    for i to n1 do
        for j to m1 do
                P[i,j]:= evalr(A[i,j] + B[i,j]);
        od;
    od;
P;
end:

# Matrix Substruction with evalr
mat_sub := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if n1<>n2 or m1<>m2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m1);
    for i to n1 do
        for j to m1 do
                P[i,j]:= evalr(A[i,j] - B[i,j]);
        od;
    od;
P;
end:

# Evaluate Polynomial Matrix on intervals
eval_on_ints:= proc( var::list ,int::list , M::Matrix )
local E, n,m,i,j;

    #print(`Eval_on_ints IN:`, var, int, M );
    n,m:= Dimension(M);
    E:= Matrix(n,m);

    for i to n do
        for j to m do
            E[i,j]:= evalr( subs( seq( var[j]=int[j], j=1..nops(var)) , M[i,j]  ) ) ;
od:
od:
E;
end:

# Compute X+xs with X interval and xs value
X_xs:= proc( X::list, xs::list)
    local i, E;
    E:=X;

    for i to nops(X) do
        E[i]:= evalr( X[i]+ xs[i]);
    od;
E;
end:

#Interval box for use in rump's test
i_box:= proc( bx::list, nvars::integer, tol:=0.01 )
local i,zs,n, X,cc ;
    n:= nops(bx);

    zs:= [ seq( (bx[i][1]+bx[i][2])/2, i=1..nops(bx) ),
           seq( 0, i=1..nvars-nops(bx) )     ];

    X:=NULL;
    for i to nops(bx) do
        cc:=bx[i]- [zs[i], zs[i]];
        X:= X, INTERVAL(cc[1]..cc[2]);
    od:
    X:= X, seq( INTERVAL(-tol..tol),j= nops(bx)+1..nops(zs) ) ;

#print(`i_box: `, zs );
zs ,[X] ;
end:

# Make a box around z with certain tolerance
mbox:= proc (z::list, tol:=0.02)
[seq( [z[j]-tol,z[j]+tol], j=1..nops(z))];
end:


# Return starting value of interval
istart:= proc ( a)
if whattype(a)=function then
RETURN(op( op(a) )[1]);
else
RETURN(a);
fi:
end:

# Return ending value of interval
iend:= proc ( a )
if whattype(a)=function then
RETURN(op( op(a) )[2]);
else
RETURN(a);
fi:
end:

#Checks if a is included in b
inclusion:= proc ( a, b) #a:function or number
    #print(`inclusion IN:`,a,b);
istart(a)>istart(b) and iend(a)<iend(b);
end:

############################################################
###  END-------------------------Deflation, Root Isolation------------------------------
############################################################



###########################################################
###########################################################
### Benchmark Systems
###########################################################
###########################################################
bench_systems := proc()
local dd, z0,z1,z2, G,v,p ;

#############################
# Systems
#############################
G:=[seq(0,k=1..12) ];
p:=[seq(0,k=1..12) ];
v:=[seq(0,k=1..12) ];

#1. cbms1:
G[1]:=[
x[1]^3 - x[2]*x[3],
x[2]^3 - x[1]*x[3],
x[3]^3 - x[1]*x[2]
];
p[1]:= [ [0, 0, 0] ,0 ];
v[1]:= get_var(nops(%[1]));

#2. cbms2:
G[2]:=[
x[1]^3 - 3*x[1]^2*x[2] + 3*x[1]*x[2]^2 - x[2]^3 - x[3]^2,
x[3]^3 - 3*x[3]^2*x[1] + 3*x[3]*x[1]^2 - x[1]^3 - x[2]^2,
x[2]^3 - 3*x[2]^2*x[3] + 3*x[2]*x[3]^2 - x[3]^3 - x[1]^2
];
p[2]:= [ [0, 0, 0], 0 ];
v[2]:= get_var(nops(%[1]));

#3. mth191:
G[3]:=[
x[1]^3 + x[2]^2 + x[3]^2 - 1,
x[1]^2 + x[2]^3 + x[3]^2 - 1,
x[1]^2 + x[2]^2 + x[3]^3 - 1
];
p[3]:=[ [0, 1, 0], 0 ];
v[3]:= get_var(nops(%[1]));

#4. decker2:
G[4]:=[
x[1] + x[2]^3,
x[1]^2*x[2] - x[2]^4
];
p[4]:= [ [0, 0], 0 ];
v[4]:= get_var(nops(%[1]));

#5. Ojika2:
G[5]:=[
x[1]^2 + x[2] + x[3] - 1,
x[1] + x[2]^2 + x[3] - 1,
x[1] + x[2] + x[3]^2 - 1
];
p[5]:=[
#[0, 0, 1],  0,
[1, 0, 0]  , 0
];
v[5]:= get_var(nops(%[1]));

#6. Ojika3:
G[6]:=[
x[1] + x[2] + x[3] - 1,
2*x[1]^3 + 5*x[2]^2 - 10*x[3] + 5*x[3]^3 + 5,
2*x[1] + 2*x[2] + x[3]^2 - 1
];
p[6]:=[
[0, 0, 1], 0
#,[-5/2, 5/2, 1], 0
];
v[6]:= get_var(3);

#7. KSS:
G[7]:=[
x[1]^2-2*x[1] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[2]^2-2*x[2] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[3]^2-2*x[3] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[4]^2-2*x[4] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[5]^2-2*x[5] + x[1]+x[2]+x[3]+x[4]+x[5]-4
];
p[7]:= [ [1,1,1,1,1] , 0];
v[7]:= get_var(nops(%[1]));

#8. Caprasse:
G[8]:=[
-x[1]^3*x[3] +4*x[1]*x[2]^2*x[3] +4*x[1]^2*x[2]*x[4] +2*x[2]^3*x[4] +4*x[1]^2 -10*x[2]^2 +4*x[1]*x[3] -10*x[2]*x[4] +2,
-x[1]*x[3]^3+4*x[2]*x[3]^2*x[4]+4*x[1]*x[3]*x[4]^2+2*x[2]*x[4]^3+4*x[1]*x[3]+4*x[3]^2- 10*x[2]*x[4]- 10*x[4]^2+ 2,
x[2]^2*x[3] +2*x[1]*x[2]*x[4] -2*x[1] -x[3],
x[1]*x[4]^2 +2*x[2]*x[3]*x[4] -x[1] -2*x[3]
];
p[8]:= [ [ 2, -I*sqrt(3), 2, I*sqrt(3) ] , 0.0001]; #exact
v[8]:= get_var(nops(%[1]));

#9. Cyclic nine:
G[9]:= [
x[1]+x[2]+x[3]+x[4]+x[5]+x[6]+x[7]+x[8]+x[9],
x[1]*x[2]+x[2]*x[3]+x[3]*x[4]+x[4]*x[5]+x[5]*x[6]+x[6]*x[7]+x[7]*x[8]+x[8]*x[9]+x[9]*x[1],
x[1]*x[2]*x[3]+x[2]*x[3]*x[4]+x[3]*x[4]*x[5]+x[4]*x[5]*x[6]+x[5]*x[6]*x[7]+x[6]*x[7]*x[8]+x[7]*x[8]*x[9]+x[8]*x[9]*x[1]+x[9]*x[1]*x[2],
x[1]*x[2]*x[3]*x[4]+x[2]*x[3]*x[4]*x[5]+x[3]*x[4]*x[5]*x[6]+x[4]*x[5]*x[6]*x[7]+x[5]*x[6]*x[7]*x[8]+x[6]*x[7]*x[8]*x[9]+x[7]*x[8]*x[9]*x[1]+x[8]*x[9]*x[1]*x[2]+x[9]*x[1]*x[2]*x[3],
x[1]*x[2]*x[3]*x[4]*x[5]+x[2]*x[3]*x[4]*x[5]*x[6]+x[3]*x[4]*x[5]*x[6]*x[7]+x[4]*x[5]*x[6]*x[7]*x[8]+x[5]*x[6]*x[7]*x[8]*x[9]+x[6]*x[7]*x[8]*x[9]*x[1]+x[7]*x[8]*x[9]*x[1]*x[2]+x[8]*x[9]*x[1]*x[2]*x[3]+x[9]*x[1]*x[2]*x[3]*x[4],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7],
1-x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]
];
z1:=-1/4*(-36-16*I*15^(1/2)-4*(-163+72*I*15^(1/2))^(1/2))^(1/3)-1/4*I*3^(1/2)*(-36-16*I*15^(1/2)-4*(-163+72*I*15^(1/2))^(1/2))^(1/3):
z0:=subs(x1=z1, 6765/2584*x1-1/2584*x1^10):
z2:=3*z0-z1:
dd:= Digits:
Digits:=5:
p[9]:=[
evalf
([z0,z1,z2,z0,-z2,-z1,z0,-z2,-z1]) , 0.0001];
Digits:=dd:
v[9]:= [seq(x[i],i=1..9)];

#10. DZ1:
G[10]:= [
x[1]^4 -x[2]*x[3]*x[4],
x[2]^4 -x[1]*x[3]*x[4],
x[3]^4 -x[1]*x[2]*x[4],
x[4]^4 -x[1]*x[2]*x[3]
];
p[10]:= [ [0, 0, 0, 0] , 0.00001]; #exact
v[10]:= get_var(nops(%[1]));

#11. DZ2:
G[11]:= [
x[1]^4,
x[1]^2*x[2] + x[2]^4,
x[3] + x[3]^2 - 7*x[1]^3 - 8*x[1]^2
];
p[11]:= [ [0, 0, -1] , 0];
v[11]:= get_var(nops(%[1]));

#12. DZ3:
G[12]:= [
14*x[1] + 33*x[2] - 3*sqrt(5)* (x[1]^2 + 4*x[1]*x[2] + 4*x[2]^2 + 2) + sqrt(7) + x[1]^3 + 6*x[1]^2*x[2] + 12*x[1]*x[2]^2 + 8*x[2]^3,
41*x[1] - 18*x[2] - sqrt(5) + 8*x[1]^3 - 12*x[1]^2*x[2] + 6*x[1]*x[2]^2 - x[2]^3 + 3*sqrt(7)*(4*x[1]*x[2] - 4*x[1]^2 - x[2]^2 - 2)
];
# with coeffcients rounded to 5 digits, at approximate zero
#dd:=Digits;
#Digits:=5;
#Digits:=dd;
#p[12]:= [  [1.5055, 0.36528] , 0.0005 ];
# Exact Root: [ (2/5)*7^(1/2)+(1/5)*5^(1/2),-(1/5)*7^(1/2)+(2/5)*5^(1/2)];
p[12]:=[ [ (2/5)*7^(1/2)+(1/5)*5^(1/2),-(1/5)*7^(1/2)+(2/5)*5^(1/2)], 0];

v[12]:= get_var(nops(%[1]));


##
## More instances
##

# Ojika87
#f1 := x[1]^2+x[2] - 3 ;
#f2 := x[1] + 1/8*x[2]^2 -3/2 ;
#z:=[1,2]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

#RumpGr-success
#f1 := x[1]^2 - x[2]^2 ;
#f2 := x[1]   - x[2]^2 ;
#z:=[0,0]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

#RumpGr-fail
#f1 := x[1]^2*x[2] - x[1]*x[2]^2 ;
#f2 := x[1] - x[2]^2 ;
#z:=[0,0]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

G,p,v;
end:


#
# Run tests !
#
run_tests := proc(test::integer )
local k, RTA, Db, A, RT, i,j, G,v,p, res, DF, sol;

# Settings
Digits:= 32:
interface(displayprecision = 5):
interface(rtablesize=30):

G,p,v := bench_systems();
#print(G);
#print(v);
#print(p);

#############################
# Compute Dual Basis test
#############################
if test=1 then
#############################

#lprint("Running times: macaulay0, macaulay, mourrain0, mourrain,
# basis_pair");
#lprint("Running times: macaulay, mourrain0, mourrain, dualBasisNew");
lprint("Running times. macaulay0, mourrain0, mourrain, mourrainOPT, new, newOPT");

    res:=NULL;
    RTA := 0;k:=1:
    # NOTE: all benchmarks are for i in seq([1..12])
    #for i in [3,9] do
    for i in [seq(10..12)] do
                print("--- System :",i, " --- ", p[i][1], " --- tol:", p[i][2]);
                RT:=
                [
                    # Macaulay (plain)
                    #time( macaulay0  (G[i],v[i],p[i][1],p[i][2] ) ),

                    # Integration (plain)
                    #time( mourrain0  (G[i],v[i],p[i][1],p[i][2] ) ),

                    # Integration with MM11 (plain)
                    time( mourrain   (G[i],v[i],p[i][1],p[i][2], infinity, false, true ) )

                    # Integration with MM11 (optimized)
                    ,time( mourrain   (G[i],v[i],p[i][1],p[i][2], infinity, true, true ) )
                    
                    # New Alg. (plain)
                    ,time( dualBasisNew (G[i],v[i],p[i][1],p[i][2], infinity, false ) )

                    # New Alg. (optimized)
                    ,time( dualBasisNew (G[i],v[i],p[i][1],p[i][2], infinity, true ) )

#                    time( basis_pair (G[i],v[i],p[i][1],p[i][2] ) )
#                time( ApaTools[MultiplicityStructure](G[i],v[i],p[i][1],p[i][2]) ),
                ];
                RTA := RTA * (k-1)/k  +  RT / k ;
            #print("Rta:", RTA );
            res:= res, RTA;
        ##od;
        #print(basis_pair(G[i],v[i],p[i][1],p[i][2]) );
    od;
fi;

#############################
# Matrix sizes test
#############################
if test=2 then
#############################

lprint("Deflation");

    res:=NULL;
    for i to nops(G) do
        print("--- System :",i, " --- ", p[i][1], " --- tol:", p[i][2]);

        #Db, A := mourrain (G[i],v[i],p[i][1],p[i][2] );

        DF:= deflate_lin (G[i],v[i],p[i][1], p[i][2]);
        sol:= fsolve(DF[1]);
        #print("Sols:", seq(sol[k][1..nops(v[i])], k=1..nops(sol)) );
        print("Sols:", sol );


    od;
fi;

#############################
# Certify root test
#############################
if test=3 then
#############################
    for i in [9]  do
        for j to nops(p[i]) do
            print("--",i,"--", p[i][j], "--");
            Db, A := mourrain(G[i],v[i],p[i][j]);
            print( nops( Db ) );
            print("Mac_Dim:", mac_dim(nops(G[i]),nops(v[i]), degree(to_polynomial(Db[-1], v[i]))+1 ) );
        od;
    od;
fi;

[res];
end:

###########################################################
###END------------------- Benchmark Systems---------------------------------------
###########################################################


####################################################
###END-----------use packages---------
end use;
end use;
end use;
end use;
#end use;
####################################################

####################################################
###END------------module end-------------------
lprint(`Multiple Roots package`);
end:
####################################################

####################################################
####################################################
###Settings and Procedure Analyzer
#######s#############################################
#######s#############################################
# Settings
UseHardwareFloats := true: #Using hardware floats
Digits:= 32:


##
## procedure analyzer
##
mmint := proc( f,
  {level::posint:=2},
  {toggle::list(posint):=[]},
  {header::truefalse:=false},
  {extras::string:=""} )
local fname,k,oldiface,executable;
   fname := cat(kernelopts('homedir'),kernelopts('dirsep'),"minttemp.txt");
   #fname := "/tmp/minttemp.txt"; # or some other temp location
   oldiface := interface('verboseproc');
   interface('verboseproc'=3);
   writeto(fname);
   printf("%a := %a:\n", f, eval(f));
   writeto(terminal):
   fclose(fname);
   interface('verboseproc'=oldiface);
   executable:=`if`(kernelopts('platform')="windows",
      cat("\"",kernelopts('bindir'),"\\mint","\""),
      cat(kernelopts('mapledir'),kernelopts('dirsep'),"bin/mint"));
   k:=ssystem(cat(executable, cat(" -i ",min(level,4)," "),
                  seq(cat(" -t ",x," "), x in remove(t->t>32,toggle)),
                  `if`(not(header)," -q ",NULL),
                  " ",extras," ","\"",fname,"\""));
   if k[1]>=0 then printf("%s",k[2]); end if;
   NULL;
end proc:
#Warning, `mourrain_matrix_new` is implicitly declared local to `module` #`mroot`
#`Multiple Roots package`

####################################################
###END-----------------------------Settings and Procedure Analyzer-------
#######s#############################################



