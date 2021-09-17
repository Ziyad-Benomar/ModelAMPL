# MINOA Challenge
# Author: Benomar Ziyad
# 05/03/21

##############################################################################################
##############################################################################################
#"""""""""""""""""""""""""""""          Parameters        """"""""""""""""""""""""""""""""""""
##############################################################################################
##############################################################################################


## The sub-PTN (public transportation network graph)
# Subset of the nodes (bus stops)
set N; # set of nodes
param O symbolic; # depot
set Np := N union {O};

## Time parameters
# Any time-related quantity is expressed as an integer
param k, integer, >=0; # number of time windows 
param t{i in {0..k}}, integer, >=0, <=86400; # Instants defining the time windows (in seconds)
set H := {1..k}; # set of timewindows (H here is not the time horizon)
set time_seconds := {t[0]..t[k]};
param time_window{tsec in time_seconds} := card{l in {0..k} : tsec>t[l]};

## Trips
# a trip i is a direction + starting time + ending time + arrival time at the main stop + length
set TS; #set of the trips set T (defined in the run file)
param sn{TS} symbolic; #start node
param en{TS} symbolic; #end node
param st{TS}; #start time
param et{TS}; #end time
param a{TS}; #arrival time at the main stop 
param h{i in TS} := time_window[a[i]]; #time window when the vehicle arrives to the main stop (maybe needs to be defined in the run file)
param l{TS}; #length of the trip (km)
param init_final{TS} symbolic;

param w{i in TS,j in TS} = a[j] - a[i]; # This parameter is needed for writing the TT constraints

# Number of trips in each direction 
param count_trips{n1 in N, n2 in N} := card{i in TS : sn[i]=n1 and en[i]=n2};


## Maximum headway for each line, for each direction, and between two trips
param I{N,N,H}; #
param I_max{i in TS, j in TS : sn[i]=sn[j] and en[i]=en[j]} := max(I[sn[i],en[i],h[i]], I[sn[j],en[j],h[j]]);


# Set of indices
set indTS := {1..card{TS}};
set indTSm1 := {1..card{TS}-1};

## Min and max stopping time (in seconds)
param delta_min{H,Np} integer, >=0; #min stopping time
param delta_max{H,Np} integer, >=0; #max stopping time
param delta_min_O{H}  integer, >=0; #min stopping time at the depot
# a break is when a vehicle stays at a node after delta_min while it is not being recharged


## Durations and lengths of deadhead trips
param tp{H,N} integer, >=0; # duration of a pull-in trip
param tm{H,N} integer, >=0; # duration of a pull-out trip
param lp{N} >=0; # length of a pull-in trip
param lm{N} >=0; # length of a pull-out trip


# Number of available electric and non-electric vehicles
param num_ele_vehicles integer, >=0; # 
param num_ice_vehicles integer, >=0, default 2*num_ele_vehicles;


set B = 1..num_ele_vehicles+num_ice_vehicles; # Set of all vehicles
set BE = 1..num_ele_vehicles; # Set of electric vehicles
set BI = num_ele_vehicles+1..num_ele_vehicles+num_ice_vehicles; # Set of ICE vehicles


## Electricity/recharging parameters
param phi >0, <1; # fast recharge coeff
param cap{Np} integer, >=0; # parking capacity
param slowCC{Np} integer, >=0; # slow charging capacity
param fastCC{Np} integer, >=0; # fast charging capacity

# EV parameters (We assume that there is only only one type of electic vehicles)
param tR_max integer, >=0; # maximum charging time
param tR_min integer, >=0; # minimum charging time
param a_tot; # Autonomy (in km)

# Cost parameters
param C_CO2_ice;

set v := {"ICE", "electric"};
param c{v};
param cpio{v};
param cBreak;



##############################################################################################
##############################################################################################
#"""""""""""""""""""""""""""""          Variables         """"""""""""""""""""""""""""""""""""
##############################################################################################
##############################################################################################

# performed[i] = 1 iif the trip i is performed in some block b
var performed{TS} binary;

## Variables for TT constraints
# xTT[j,i] == 1 iif the trip i is the j-th trip performed in the direction st[i],en[i]
var xTT{j in indTS,i in TS : j<=count_trips[sn[i],en[i]]} binary;
# yTT[n1,n2,j] == 1 iif at least j trips are performed in the direction (n1,n2)
var yTT{n1 in N,n2 in N,j in indTS : j<=count_trips[n1,n2]} binary;
# count_perf_trips[n1,n2]=j iif j trips were performed in the direction n1,n2
var count_perf_trips{N,N} integer, >=0;
# indicates if the trip i is the last one performed in the direction n1,n2
var is_last_trip{N,N,TS} binary, default 1;
# pi[n1,n2,j] = i iif the j-th trip in the direction (n1,n2) is the trip i
var pi{i in TS} integer >=0, <= card{{j in TS : sn[j]=sn[i] and en[j]=en[i]}}, default -2;
var diff_pi_p{i in TS,j in TS : j!=i and  sn[i]=sn[j] and en[i]=en[j]} >= 0, default 0; # auxilary variable
var diff_pi_m{i in TS,j in TS : j!=i and sn[i]=sn[j] and en[i]=en[j]} >= 0, default 0; # auxilary variable
var consecutiveTT{i in TS,j in TS : j!=i and sn[i]=sn[j] and en[i]=en[j]} binary, default 0;


## Variables for VS constraints
# x[b,j,i] == 1 iif the trip i is the j-th trip performed by b
var x{B,indTS,TS} binary;
# y[b,j] == 1 iif the block b contains at least j trips
var y{B,indTS} binary; # note that y[b,1]==1 iif the bus b is used
# z[b,i] == 1 iif trip i is in the block b
var z{B,TS} binary; 
# schedule[b,i] = j iif i is the j-th trip performed by b, and =-2 otherwise
var schedule{B,TS} integer, >=0, <= card{TS}, default -2;
# consecutive[b,i1,i2] = 1 iif i1,i2 are consecutive trips in the block b
var diff_schedule_p{B,TS,TS} >= 0; # auxilary variable
var diff_schedule_m{B,TS,TS} >= 0; # auxilary variable
var consecutive{B,TS,TS} binary;
# Variables for the first node of each trip in each block
var t_stop1{B,indTS} integer, >=0, default 0; # stop time at the first node of the trip
var t_break1{B,indTS} integer, >=0, default 0;
var t_fast1{BE,indTS} integer, >=0, default 0; # fast charging time at the first node of the trip
var t_slow1{BE,indTS} integer, >=0, default 0;
var recharge1{BE,indTS} binary, default 0; # deciding to recharge or not
var a_res1{BE,indTS} >=0; # residual autonomy when arriving to the node
# Variables for the second node of each trip in each block
var t_stop2{B,indTS} integer, >=0, default 0;
var t_break2{B,indTS} integer, >=0, default 0;
var t_fast2{BE,indTS} integer, >=0, default 0;
var t_slow2{BE,indTS} integer, >=0, default 0;
var recharge2{BE,indTS} binary, default 0;
var a_res2{BE,indTS} >=0; # residual autonomy when arriving to the node
# Variables for an eventual back to the depot before a trip
var t_stop0{B,indTS} integer, >=0, default 0;
var t_break0{B,indTS} integer, >=0, default 0;
var t_fast0{BE,indTS} integer, >=0, default 0;
var t_slow0{BE,indTS} integer, >=0, default 0;
var recharge0{BE,indTS} binary, default 0;
var a_res0{BE,indTS} >=0, default 0;
# Variables to decide if we go the depot before a trip or not
var back_depot{B,indTS} binary; # decides if the bus goes to the depot before its j-th trip
# Auxilary variables needed for the constraints on stopping time
var tch_minus_deltamin_p0{BE,indTS} >=0;
var tch_minus_deltamin_m0{BE,indTS} >=0;
var tch_minus_deltamin_p1{BE,indTS} >=0;
var tch_minus_deltamin_m1{BE,indTS} >=0;
var tch_minus_deltamin_p2{BE,indTS} >=0;
var tch_minus_deltamin_m2{BE,indTS} >=0;


## Variables for writing the objective function (the constraints defining these are in the end
# of this modeling file)
var t_break_tot{B} integer, >=0;
var t_deadhead_tot{B} integer, >=0;
var d_tot{BI} integer, >=0;


##############################################################################################
##############################################################################################
#"""""""""""""""""""""""""""""     Objective function     """"""""""""""""""""""""""""""""""""
##############################################################################################
##############################################################################################

minimize total_cost:
    sum{b in BE} (c["electric"] + cBreak*t_break_tot[b] + cpio["electric"]*t_deadhead_tot[b]) 
    + sum{b in BI} (c["ICE"] + cBreak*t_break_tot[b] + cpio["ICE"]*t_deadhead_tot[b] + C_CO2_ice*d_tot[b])
;



##############################################################################################
##############################################################################################
#"""""""""""""""""""""""""""""         Constraints        """"""""""""""""""""""""""""""""""""
##############################################################################################
##############################################################################################

##*******************************************************************************************
## TT constraints
##*******************************************************************************************

# This constraint garantees that once a value yTT[n1,n2,j]=0, all the following values (j) are also 0
subject to first_trips_TT{n1 in N, n2 in N, j in indTS : j<count_trips[n1,n2]}:
    yTT[n1,n2,j+1] <= yTT[n1,n2,j];

# With the previous constraint, the following one garantees that x[n1,n2,j,i]=1 iif i is the j-th trip in the direction (n1,n2)
subject to one_jth_TT{n1 in N, n2 in N, j in indTS : j<=count_trips[n1,n2]}:
    sum{i in TS : sn[i]=n1 and en[i]=n2} xTT[j,i] = yTT[n1,n2,j];

subject to def_count_perf_trips{n1 in N,n2 in N}:
    count_perf_trips[n1,n2] = sum{j in indTS : j<=count_trips[n1,n2]} yTT[n1,n2,j];

# This defintion garantees that pi[i]==-2 iif the trip i is not performed
# and ==j if the trip i is the j-th trip in the direction (sn[i],en[i])
subject to def_pi{i in TS}: 
    pi[i] = -2 + sum{j in indTS : j<=count_trips[sn[i],en[i]]} (j+2)*xTT[j,i];

# Now we define the positive/negative parts of (schedule[b,i2]-schedule[b,i1]-1) in order to use its absolute value
subject to abs_diff_pi1{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}:
    pi[i2] - pi[i1] -1 = diff_pi_p[i1,i2] - diff_pi_m[i1,i2];

subject to abs_diff_pi2{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}:
    diff_pi_p[i1,i2]*diff_pi_m[i1,i2] = 0;

# If we want to define it using the var schedule, it would be  consecutive[b,i1,i2] := (schedule[b,i2]-schedule[b,i]==1 and z[b,i1]==1)
subject to def_consecutive_TT1{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}:
    1 - consecutiveTT[i1,i2] <= diff_pi_p[i1,i2] + diff_pi_m[i1,i2];

subject to def_consecutive_TT2{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}: # is this constraint necessary if we set consecutive[] default 0
    (1 - consecutiveTT[i1,i2])*2*card{indTS} >= diff_pi_p[i1,i2] + diff_pi_m[i1,i2];
# The factor 2*card{indTS} is an upper bound for the right term, therefore if this one is non null, then 1-consecutive[b,i1,i2]  is not either

# Two consecutive trips i1,i2 must verify a[i1] <= a[i2]
subject to ordered_passing_main_stop{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}:
    w[i1,i2]*consecutiveTT[i1,i2] >= 0;

# Note that if consecutiveTT[n1,n2,i1,i2], then h[i2]-h[i1] is necessarily in {0,1} (last lines in TT constraints)
subject to max_headway1{i1 in TS,i2 in TS : i1!=i2 and sn[i1]=sn[i2] and en[i1]=en[i2]}:
    consecutiveTT[i1,i2]*(w[i1,i2] - I_max[i1,i2]) <= 0;

# The first trip in every direction must be in the set of allowed first trips
subject to initial_trip{n1 in N,n2 in N}:
    sum{i in TS : sn[i]=n1 and sn[i]=n2 and init_final[i] = "initial"} xTT[1,i] = 1;

# the last trip
subject to last_trip1{n1 in N, n2 in N, i in TS} :
    1-is_last_trip[n1,n2,i] <= count_perf_trips[n1,n2] - pi[i];

subject to last_trip2{n1 in N, n2 in N, i in TS} :
    1-is_last_trip[n1,n2,i]*card{TS} >= count_perf_trips[n1,n2] - pi[i];


# The last trip in every direction must be in the set of allowed final trips
subject to final_trip{n1 in N,n2 in N}:
    sum{i in TS : sn[i]=n1 and sn[i]=n2 and init_final[i] = "final"} is_last_trip[n1,n2,i] = 1;




##********************************************************************************************
## VS constraints
##********************************************************************************************

## Auxilary VS constraints : Defining x, y, z, schedule, consecutive
##-------------------------------------------------------------------------------------------

## Constraints on x, y, schedule, consecutive, to garantee they correctly mean what we want them to
# This constraint garantees that once a value y[b,j]=0, all the following values (j) are also 0
subject to first_trips{b in B, j in indTSm1}:
    y[b,j+1] <= y[b,j];

# With the previous constraint, the following one garantees that x[b,j,i]=1 iif i is the j-th trip in the block b
subject to one_jth{b in B, j in indTS}:
    sum{i in TS} x[b,j,i] = y[b,j];
# Maybe it is possible not to define y, and just write the previous constraints using x

# The following constraint garantees the interpretation we gave to z[b,i] : z[b,i] == 1 iif trip i is in the block b
subject to def_z{b in B, i in TS}:
    z[b,i] = sum{j in indTS} x[b,j,i];

# This defintion garantees that schedule[b,i]==-2 if the trip i is not in the block b 
subject to def_schedule{b in B, i in TS}: 
    schedule[b,i] = -2 + sum{j in indTS} (j+2)*x[b,j,i]; #sum{j in indTS} j*x[b,j,i]

# Now we define the positive/negative parts of (schedule[b,i2]-schedule[b,i1]-1) in order to use its absolute value x = xp - xm, |x| = xp + xm
subject to abs_diff_schedule1{b in B, i1 in TS, i2 in TS}:
    schedule[b,i2] - schedule[b,i1] -1 = diff_schedule_p[b,i1,i2] - diff_schedule_m[b,i1,i2];

subject to abs_diff_schedule2{b in B, i1 in TS, i2 in TS}:
    diff_schedule_p[b,i1,i2]*diff_schedule_m[b,i1,i2] = 0;

# If we want to define it using the var schedule, it would be  consecutive[b,i1,i2] := (schedule[b,i2]-schedule[b,i1]==1)
subject to def_consecutive1{b in B, i1 in TS, i2 in TS}:
    1 - consecutive[b,i1,i2] <= diff_schedule_p[b,i1,i2] + diff_schedule_m[b,i1,i2];

subject to def_consecutive2{b in B, i1 in TS, i2 in TS}: # is this constraint necessary if we set consecutive[] default 0
    (1 - consecutive[b,i1,i2])*2*card{indTS} >= diff_schedule_p[b,i1,i2] + diff_schedule_m[b,i1,i2];
# The factor 2*card{indTS} is an upper bound for the right term, therefore if this one is non null, then 1-consecutive[b,i1,i2]  is not either


## In-line / Out-line compatibility
##-------------------------------------------------------------------------------------------

# in-line compatibility (the constraints from 3.2.1 are active only when a vehicle does both trips i and j, with i done before j
# That's why we have the condition st[j]>=et[i], and why we multiply by z[b,j]*z[b,i] (=1 iif b performs both trips)
subject to in_line_compatibility1{b in B, i in TS, j in TS : en[i]==sn[j]}:
    consecutive[b,i,j]*(delta_min[h[i],en[i]] - (st[j] - et[i])) <= 0;

subject to in_line_compatibility2{b in B, i in TS, j in TS : st[j]>=et[i] and en[i]==sn[j]}:
    schedule[b,i]*(delta_max[h[i],en[i]] - (st[j] - et[i])) >= 0;

# out-line compatibility
subject to out_line_compatibility{b in B, i in TS, j in TS : en[i]!=sn[j]}:
    consecutive[b,i,j]*( (st[j] - et[i]) - (tp[h[i],en[i]] + delta_min_O[h[i]] + tm[h[j],sn[j]]) ) >= 0;

# Initialy, all the vehicles are in the depot
subject to initialy_at_depot{b in B}:
    back_depot[b,1] = 1;


## Back to the depot ?
##-------------------------------------------------------------------------------------------

# if the end node of the trip j and the the start node of the trip j+1 are different, then the bus is obliged to go back to the depot
subject to back_to_the_depot1{b in B, j in indTSm1}:
    (sum{i in TS} x[b,j+1,i]*sn[i] - sum{i in TS} x[b,j,i]*en[i])*(1 - back_depot[b,j+1]) = 0;


##********************************************************************************************
## Electric constraints
##********************************************************************************************

## If the end node of the j-th trip in the block b is the same as the start node of j+1-th trip
##-------------------------------------------------------------------------------------------

# Going from the end node of a trip to the start node of the next trip
# If the bus does not go back to depot, the end node of the j-th trip and the start node of the (j+1)-th trip are the same
subject to  same_residual_autonomy_21{b in BE, j in indTSm1}:
    (a_res1[b,j+1] - a_res2[b,j])*(1 - back_depot[b,j+1]) = 0;

subject to  same_slow_recharging_decision_21{b in BE, j in indTSm1}:
    (recharge1[b,j+1] - recharge2[b,j])*(1 - back_depot[b,j+1]) = 0;

subject to  same_fast_recharging_time_21{b in BE, j in indTSm1}:
    (t_fast1[b,j+1] - t_fast2[b,j])*(1 - back_depot[b,j+1]) = 0;

subject to  same_slow_recharging_time_21{b in BE, j in indTSm1}:
    (t_slow1[b,j+1] - t_slow2[b,j])*(1 - back_depot[b,j+1]) = 0;

subject to  same_break_time_21{b in B, j in indTSm1}: ##### NOT ELECTRIC CONSTRAINT
    (t_break1[b,j+1] - t_break2[b,j])*(1 - back_depot[b,j+1]) = 0;

subject to  same_stop_time_21{b in B, j in indTSm1}: ##### NOT ELECTRIC CONSTRAINT
    (t_stop1[b,j+1] - t_stop2[b,j])*(1 - back_depot[b,j+1]) = 0;


# Recharging constraints
#--------------------------------------------------------------------------------

# At the depot (before trip j), it depends on wether bus comes to the depot or not

# We can't use slow and fast recharging at a same node
subject to slow_xor_fast_recherge0{b in BE, j in indTS}:
    t_slow0[b,j]*t_fast0[b,j] = 0;

# We can recharge at the depot only if we go back to the depot...
subject to recharge_only_if_back_depot{b in B, j in indTS}:
    recharge0[b,j] <= back_depot[b,j];

# min recharging time
subject to min_recharging_time0{b in BE, j in indTS}:
    t_slow0[b,j] + t_fast0[b,j] >= tR_min*recharge0[b,j];

# max recharging time
subject to max_recharging_time0{b in BE, j in indTS}:
    t_slow0[b,j] + t_fast0[b,j]/phi <= tR_max/a_tot*(a_tot - a_res0[b,j])*recharge0[b,j];

#--------------------------------------------------------------------------------
# At the first node of a trip

# We can't use slow and fast recharging at a same node
subject to slow_xor_fast_recherge1{b in BE, j in indTS}:
    t_slow1[b,j]*t_fast1[b,j] = 0;
# min recharging time
subject to min_recharging_time1{b in BE, j in indTS}:
    t_slow1[b,j] + t_fast1[b,j] >= tR_min*recharge1[b,j];
# max recharging time
subject to max_recharging_time1{b in BE, j in indTS}:
    t_slow1[b,j] + t_fast1[b,j]/phi <= tR_max/a_tot*(a_tot - a_res1[b,j])*recharge1[b,j];

#--------------------------------------------------------------------------------
# At the second node of a trip

# We can't use slow and fast recharging at a same node
subject to slow_xor_fast_recherge2{b in BE, j in indTS}:
    t_slow2[b,j]*t_fast2[b,j] = 0;
# min recharging time
subject to min_recharging_time2{b in BE, j in indTS}:
    t_slow2[b,j] + t_fast2[b,j] >= tR_min*recharge2[b,j];
# max recharging time
subject to max_recharging_time2{b in BE, j in indTS}:
    t_slow2[b,j] + t_fast2[b,j]/phi <= tR_max/a_tot*(a_tot - a_res2[b,j])*recharge2[b,j];



#  Residual autonomy constraints
#--------------------------------------------------------------------------------

# If the bus was at the depot before the current trip
# Constraints for the trajectory between the depot (before trip j) and the start node of the j-th trip (pull-in trip)
subject to  residual_autonomy_01{b in BE, j in indTS}:
    (a_res1[b,j] - (a_res0[b,j] + a_tot/tR_max*(t_slow0[b,j] + t_fast0[b,j]/phi) - sum{i in TS} x[b,j,i]*lm[sn[i]]))*back_depot[b,j] = 0;
# The second term corresponds the added autonomy after recharging, and the second to to the consumed autonomy during the trajectory from the end node of the trip to the depot

# Performing a trip : going from the start node (n1) of a trip to its end node (n2)
subject to residual_autonomy_12{b in BE, j in indTS}:
    a_res2[b,j] = a_res1[b,j] + a_tot/tR_max*(t_slow1[b,j] + t_fast1[b,j]/phi) - sum{i in TS} x[b,j,i]*l[i];
# The second term corresponds the added autonomy after recharging, and the second to to the consumed autonomy during the trip

# If the bus goes back to the depot before the next trip
# Constraints for the trajectory between the end node of the j-th trip and the depot (pull-out trip)
subject to  residual_autonomy_20{b in BE, j in indTSm1}:
    (a_res0[b,j+1] - (a_res2[b,j] + a_tot/tR_max*(t_slow2[b,j] + t_fast2[b,j]/phi) - sum{i in TS} x[b,j,i]*lp[en[i]]))*back_depot[b,j+1] = 0;
# The second term corresponds the added autonomy after recharging, and the second to to the consumed autonomy during the trajectory from the end node of the trip to the depot

# Initially, electrical vehicles have their max autonomy
subject to initial_residual_autonomy{b in BE}:
    a_res0[b,1] = a_tot;



##********************************************************************************************
## Stop time constraints
##********************************************************************************************

## For all vehicles (min and max stop time)

# max stop time
subject to max_stop_time1{b in B, j in indTS} :
    t_stop1[b,j] <= y[b,j] * sum{i in TS} x[b,j,i]*delta_max[h[i],sn[i]];

subject to max_stop_time2{b in B, j in indTS} :
    t_stop2[b,j] <= y[b,j] * sum{i in TS} x[b,j,i]*delta_max[h[i],en[i]];


## For ICE vehicles (relation between t_stop and t_break ==> min stop time (bc t_break>=0))
subject to break_stop_ice0{b in BI, j in indTS} :
    t_stop0[b,j] = t_break0[b,j] + y[b,j] * sum{i in TS} x[b,j,i]*delta_min_O[h[i]];

subject to break_stop_ice1{b in BI, j in indTS} :
    t_stop1[b,j] >= t_break1[b,j] + y[b,j] * sum{i in TS} x[b,j,i]*delta_min[h[i],sn[i]];

subject to break_stop_ice2{b in BI, j in indTS} :
    t_stop2[b,j] >= t_break2[b,j] + y[b,j] * sum{i in TS} x[b,j,i]*delta_min[h[i],en[i]];


## For electric vehicles (relation between t_break, t_stop, t_charge)

# depot
subject to pos1_tch_minus_deltamin0{b in BE, j in indTS}:
    t_fast0[b,j] + t_slow0[b,j] - sum{i in TS} x[b,j,i]*delta_min_O[h[i]] = tch_minus_deltamin_p0[b,j] - tch_minus_deltamin_m0[b,j];

subject to pos2_tch_minus_deltamin0{b in BE, j in indTS}:
    tch_minus_deltamin_p0[b,j] * tch_minus_deltamin_m0[b,j] = 0;

subject to break_stop_charge_elec0{b in BE, j in indTS}: # The sum of the 2 last terms is equ to max(delta_min, tcharge)
    t_stop0[b,j] = t_break0[b,j] + tch_minus_deltamin_p0[b,j] + sum{i in TS} x[b,j,i]*delta_min_O[h[i]];

# node1
subject to pos1_tch_minus_deltamin1{b in BE, j in indTS}:
    t_fast1[b,j] + t_slow1[b,j] - sum{i in TS} x[b,j,i]*delta_min[h[i],sn[i]] = tch_minus_deltamin_p1[b,j] - tch_minus_deltamin_m1[b,j];

subject to pos2_tch_minus_deltamin1{b in BE, j in indTS}:
    tch_minus_deltamin_p1[b,j] * tch_minus_deltamin_m1[b,j] = 0;

subject to break_stop_charge_elec1{b in BE, j in indTS}: # The sum of the 2 last terms is equ to max(delta_min, tcharge)
    t_stop1[b,j] = t_break1[b,j] + tch_minus_deltamin_p1[b,j] + sum{i in TS} x[b,j,i]*delta_min[h[i],sn[i]];

# node2
subject to pos1_tch_minus_deltamin2{b in BE, j in indTS}:
    t_fast2[b,j] + t_slow2[b,j] - sum{i in TS} x[b,j,i]*delta_min[h[i],en[i]] = tch_minus_deltamin_p2[b,j] - tch_minus_deltamin_m2[b,j];

subject to pos2_tch_minus_deltamin2{b in BE, j in indTS}:
    tch_minus_deltamin_p2[b,j] * tch_minus_deltamin_m2[b,j] = 0;

subject to break_stop_charge_elec2{b in BE, j in indTS}: # The sum of the 2 last terms is equ to max(delta_min, tcharge)
    t_stop2[b,j] = t_break2[b,j] + tch_minus_deltamin_p2[b,j] + sum{i in TS} x[b,j,i]*delta_min[h[i],en[i]];


## Linking constraints

subject to linking1{i in TS}:
    performed[i] = sum{b in B} sum{j in indTS} x[b,j,i];

subject to linking2{i in TS}:
    performed[i] =  sum{j in indTS : j<=count_trips[sn[i],en[i]]} xTT[j,i];




##********************************************************************************************
## Constraints defining the variables in the objective function
##********************************************************************************************

subject to total_break_time{b in B} :
    t_break_tot[b] = sum{j in indTS} (t_break0[b,j] + t_break1[b,j] + t_break2[b,j]);

subject to total_pullin_pullout_time{b in B}:
    t_deadhead_tot[b] = sum{j in indTS, i in TS} back_depot[b,j]*x[b,j,i]*tm[h[i],en[i]]
                      + sum{j in indTSm1, i in TS} back_depot[b,j+1]*x[b,j,i]*tp[h[i],en[i]];

subject to total_driving_time{b in BI}:
    d_tot[b] = t_deadhead_tot[b] + sum{i in TS} z[b,i]*(et[i] - st[i])