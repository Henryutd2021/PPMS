set production;
set factory;
set warehouse;
set store;
set res;
set renewables;


param T;
param J;

param dis{factory, warehouse};
param dis1{warehouse, store};
param p{production};
param pi{production};
param h{production};
param b{production};
param mu{production, store};
param sigam{production, store};
param v{production, res};
param w{1..J, factory, res};
param sita{renewables};
param a{renewables};
param B{renewables};
param C{renewables};
param taog{renewables};
param E{production};
param qv;
param M{production};
param N{factory, warehouse};
param wv;
param tw{warehouse};
param Ln{warehouse};
param Ls{store};
param N1{warehouse, store};
param T1{store};
param 竹k{1..J, 1..T, factory, renewables};
param 竹n{1..J, 1..T, warehouse, renewables};
param 竹s{1..J, 1..T, store, renewables};
param 耳es;
param des;
param 老b;
param 老s;
param cs;




var x{production, 1..J, factory, warehouse}>=0 integer;
var y{production, 0..J, warehouse}>=0 integer;
var z{production, 0..J, warehouse}>=0 integer;
var x1{production, 1..J, warehouse, store}>=0 integer;
var Pcgs{store, renewables}>=0 <= 18;
var Pcgk{factory, renewables}>=0 <= 18;
var Pcgn{warehouse, renewables}>=0 <= 18;
var Bk{factory, 1..J, 0..T}>=0;
var Bn{warehouse, 1..J, 0..T}>=0;
var Bs{store, 1..J, 0..T}>=0;
var Bck{factory}>=0;
var Bcn{warehouse}>=0;
var Bcs{store}>=0;
var xt{production, factory, warehouse, 1..J}>=0;
var xt1{production, warehouse, store, 1..J}>=0;
var Ebk{factory, 1..J, 1..T}>=0;
var Esk{factory, 1..J, 1..T}>=0;
var Ebn{warehouse, 1..J, 1..T}>=0;
var Esn{warehouse, 1..J, 1..T}>=0;
var Ebs{store, 1..J, 1..T}>=0;
var Ess{store, 1..J, 1..T}>=0;





minimize total_cost: sum{i in production, j in 1..J, k in factory, n in warehouse}p[i]*x[i, j, k, n]

         +sum{i in production, j in 1..J, k in factory, n in warehouse}pi[i]*dis[k, n]*x[i, j, k, n]
         
         +sum{i in production, j in 0..J, k in factory, n in warehouse}h[i]*y[i, j, n]
         
         +sum{i in production, j in 0..J, k in factory, n in warehouse}b[i]*z[i, j, n]
         
         +sum{i in production, j in 1..J, k in factory, n in warehouse, s in store}pi[i]*dis1[n, s]*x1[i, j, n, s]
         
         +sum{g in renewables, k in factory}sita[g]*a[g]*Pcgk[k, g]
         
         +sum{j in 1..J, t in 1..T, g in renewables, k in factory}taog[g]*(B[g]-C[g])*Pcgk[k, g]*竹k[j, t, k, g]
         
         +(sum{k in factory}Bck[k])*耳es*des
         
         +sum{t in 1..T, j in 1..J, k in factory}(老b*Ebk[k, j, t] - 老s*Esk[k, j, t])
         
         +sum{g in renewables, n in warehouse}sita[g]*a[g]*Pcgn[n, g]
         
         +sum{j in 1..J, t in 1..T, g in renewables, n in warehouse}taog[g]*(B[g]-C[g])*Pcgn[n, g]*竹n[j, t, n, g]
         
         +(sum{n in warehouse}Bcn[n])*耳es*des
         
         +sum{t in 1..T, j in 1..J, n in warehouse}(老b*Ebn[n, j, t] - 老s*Esn[n, j, t])
         
         +sum{g in renewables, s in store}sita[g]*a[g]*Pcgs[s, g]
         
         +sum{j in 1..J, t in 1..T, g in renewables, s in store}taog[g]*(B[g]-C[g])*Pcgs[s, g]*竹s[j, t, s, g]
         
         +(sum{s in store}Bcs[s])*耳es*des
         
         +sum{t in 1..T, j in 1..J, s in store}(老b*Ebs[s, j, t] - 老s*Ess[s, j, t]);
         


subject to supply_1{i in production, n in warehouse}: sum{k in factory}x[i, 1, k, n]+y[i, 0, n]-y[i, 1, n]+z[i, 1, n]
                                =sum{s in store}x1[i, 1, n, s];
                                
subject to supply_2{i in production, j in 2..J-1, n in warehouse}: sum{k in factory}x[i, j, k, n]+y[i, j-1, n]-y[i, j, n]-z[i, j-1, n]+z[i, j, n]
                                =sum{s in store}x1[i, j, n, s];
                                
subject to supply_3{i in production, n in warehouse}: sum{k in factory}x[i, J, k, n]+y[i, J-1, n]-y[i, J, n]-z[i, J-1, n]
                                =sum{s in store}x1[i, J, n, s];
                                
                                
subject to supply_r{i in production, j in 1..J, s in store}: sum{n in warehouse} x1[i, j, n, s]
                                >= mu[i, s]+1.28*sigam[i, s];
                                
subject to resourse{k in factory, r in res, j in 1..J}:sum{i in production, n in warehouse}v[i, r]*x[i, j, k, n]<=w[j, k, r];

subject to inv0{i in production, n in warehouse}: y[i, 0, n]=0;


subject to c_1{k in factory, j in 1..J, t in 1..T}:sum{i in production, n in warehouse}(E[i]+qv*N[k, n]*dis[k, n]*M[i])*xt[i, k, n, j]
           +sum{n in warehouse}qv*N[k, n]*dis[k, n]*wv+Bk[k, j, t]-Bk[k, j, t-1]+Esk[k, j, t]-Ebk[k, j, t]
           =sum{g in renewables}taog[g]*Pcgk[k, g]*竹k[j, t, k, g];
           
subject to c_2{n in warehouse, j in 1..J, t in 1..T}:tw[n]*Ln[n]+sum{k in factory}qv*N[k, n]*dis[k, n]*wv+sum{i in production, s in store}qv*dis1[n, s]*M[i]*xt1[i, n, s, j]
           +(sum{s in store}qv*N1[n, s]*dis1[n,s]*wv)+Bn[n, j, t]-Bn[n, j, t-1]+Esn[n, j, t]-Ebn[n, j, t]
           =sum{g in renewables}taog[g]*Pcgn[n, g]*竹n[j, t, n, g];

subject to c_3{t in 1..T,j in 1..J, s in store}:T1[s]*Ls[s]+sum{n in warehouse}qv*N1[n, s]*dis1[n, s]*wv+Bs[s, j, t]-Bs[s, j, t-1]+Ess[s, j, t]-Ebs[s, j, t]
			=sum{g in renewables}taog[g]*Pcgs[s, g]*竹s[j, t, s, g];
			
		


subj to c_7{i in production, n in warehouse, k in factory, j in 1..J}:T*(xt[i, k, n, j])=x[i, j, k, n];

subj to c_8{i in production, n in warehouse, s in store, j in 1..J}:T*(xt1[i, n, s, j])=x1[i, j, n, s];


subj to c_9{k in factory}: Bk[k, 1, 0] = Bck[k];

subj to c_10{n in warehouse}: Bn[n, 1, 0] = Bcn[n];

subj to c_11{s in store}: Bs[s, 1, 0] = Bcs[s];


subj to c_15{k in factory}: Bk[k, 52, 168] = Bck[k];

subj to c_16{n in warehouse}: Bn[n, 52, 168] = Bcn[n];

subj to c_17{s in store}: Bs[s, 52, 168] = Bcs[s];


subj to c_12{t in 1..T,j in 1..J, k in factory}: Bk[k, j, t] <= Bck[k];

subj to c_13{t in 1..T,j in 1..J, n in warehouse}: Bn[n, j, t] <= Bcn[n];

subj to c_14{t in 1..T,j in 1..J, s in store}: Bs[s, j, t] <= Bcs[s];


subj to c_21{k in factory, j in 2..J}: Bk[k, j, 0] = Bk[k, j-1, T];

subj to c_22{n in warehouse, j in 2..J}: Bn[n, j, 0] = Bn[n, j-1, T];

subj to c_23{s in store, j in 2..J}: Bs[s, j, 0] = Bs[s, j-1, T];










