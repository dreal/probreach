clear

syms Q1 Q2 S1 S2 I x1 x2 x3 ub

syms Fc01 k12 FR EGP0 tmaxI VI ke ka1 ka2 ka3 kb1 kb2 kb3

eqns = 	[	
			-Fc01 - x1 * Q1 + k12 * Q2 - FR + EGP0 * (1 - x3) == 0 
			x1 * Q1 - (k12 + x2) * Q2 == 0 
			ub - S1 / tmaxI == 0
			(S1 - S2) / tmaxI == 0
			S2 / (tmaxI * VI) - ke * I == 0
			- ka1 * x1 + kb1 * I == 0
			- ka2 * x2 + kb2 * I == 0
			- ka3 * x3 + kb3 * I == 0
%            Q1 - 110 * 16 / 18 == 0
%             Fc01 - 0.97 == 0
%             k12 - 0.066 == 0
%             FR == 0
%             EGP0 - 1.61 == 0
%             tmaxI - 55 == 0
%             VI - 12 == 0
%             ke - 0.138 == 0
%             ka1 - 0.006 == 0
%             ka2 - 0.06 == 0
%             ka3 - 0.03 == 0
%             kb1 - 0.0034 == 0
%             kb2 - 0.056 == 0
%             kb3 - 0.024 == 0            
		]

sys = solve(eqns, Q2, S1, S2, I, x1, x2, x3, ub)