clc
clear
close all

global A B

% value of parameters
w = 100; % body weight
Ka1 = 0.006;
Kb1 = 0.0034;
tauI = 55;
F01 = 0.0097*w;
P0 = 0.0161*w;
Ke = 0.138;
Ka2 = 0.06;
Kb2 = 0.056;
vI = 0.12*w;
tauG = 40;
AG = 0.8;
K12 = 0.066;
Ka3 = 0.03;
Kb3 = 0.024;
vG = 0.16*w;
FR = 0;
%==================
% steady state values of variables according to nonlinear system
% ub = 0.286355;
% I0 = ub/(vI*Ke);
% x10 = Kb1*I0/Ka1;
% x20 = Kb2*I0/Ka2;
% x30 = Kb3*I0/Ka3;
% Q20 = (P0*(1-x30)-F01-FR)/x20;
% Q10 = (K12+x20)*Q20/x10;
% approximate value of the steady state of the nonlinear system
ub = 0.055485957306259535484277955219043;
I0 = 0.033506012866098753311762050253045;
x10 = 0.018986740624122626876665161810059;
x20 = 0.031272278675025503090977913569509;
x30 = 0.026804810292879002649409640202436;
Q20 = 19.085409849110653871810249291894;
Q10 = 97.777777777777777777777777777778;
%==================
% state matrix of linearzied system in continuous time
% First change of variables is performed to bring the system around the
% steady state values. Then terms with degree higher than one is eliminated
A = zeros(10);
A(1,2) = -1/(tauG^2);
A(2,1) = 1;
A(2,2) = -2/tauG;
A(3,3) = -1/tauI;
A(4,3) = 1/tauI;
A(4,4) = -1/tauI;
A(5,4) = -1/(tauI*vI);
A(5,5) = -Ke;
A(6,5) = Kb1;
A(6,6) = -Ka1;
A(7,5) = Kb2;
A(7,7) = -Ka2;
A(8,5) = Kb3;
A(8,8) = -Ka3;
A(9,6) = Q10;
A(9,7) = -Q20;
A(9,9) = -K12-x20;
A(9,10) = x10;
A(10,2) = 0.18;
A(10,6) = -Q10;
A(10,8) = -P0;
A(10,9) = K12;
A(10,10) = -x10;

B = zeros(10,2);
B(3,1) = 1;
B(2,2) = AG/0.18;

%=============================
% performing time discretization
T = 5; % sampling time (minutes)

% computing G, state transition matrix of discrete system
G = expm(A*T);

% computing H, integrating approximately
H = zeros(size(B));
n = 10000;
t = linspace(0,T,n+1);
delta = T/n;
for i=1:n
    H = H + expm(A*t(i))*B*delta;
end

%fun1 = @(t)expm(A*t)*B(:,1);
%H(:,1) = integral(fun1,0,T,'ArrayValued',true)

%fun2 = @(t)expm(A*t)*B(:,2);
%H(:,2) = integral(fun2,0,T,'ArrayValued',true)

C = zeros(1,10); % specifying the output
C(1,10) = 1;
D = [0 0];
%=============================================
% writing the system as a transfer function from input and disturbance to
% the output
%sys1 = ss(A,B,C,D);
%sys2 = ss(G,H,C,D,T);

[bp,ap] = ss2tf(G,H(:,1),C,0);
[bd,ad] = ss2tf(G,H(:,2),C,0);

% transfer function of the controller
ac = [1 -1 0]; % numerator
% bc = [a b c] denumerator should be of this form
% we can translate these a b c in terms of Kp Ki Kd
% for stability we just need to comute
% root = roots(conv(ac,ap) + conv(bc,bp));
% and then see if max(abs(root))<1
% in the following we check stability when a b c are from some intervals

%================================================
% checking stability of the closed-loop system for different [a b c]
bound1 = 0.001;
bound2 = 0.001;
bound3 = 0.001;

%===============================================
% testing a particular region based on the contoller gains
Gain_p = [-0.000675286];
Gain_i = [-2.07352e-7];
Gain_d = [-0.0416288];
value_a = Gain_p + Gain_i + Gain_d;
value_b = - Gain_p - 2* Gain_d;
value_c = Gain_d;

n = 32;
a = linspace(-bound1+value_a,bound1+value_a,n+1);
b = linspace(-bound2+value_b,bound2+value_b,n+1);
c = linspace(-bound3+value_c,bound3+value_c,n+1);

alac = zeros(n^2,3);
alac2 = zeros(length(a),length(b),length(c));
u = 0; % index for counting the number of valid gains

for i = 1:length(a)
    for j = 1:length(b)
        for k = 1:length(c)
            bc = [a(i) b(j) c(k)];
            root_i = roots(conv(ac,ap) + conv(bc,bp));
            if(max(abs(root_i))<1)
                u = u+1;
                alac(u,:) = bc;
            end
            [~,ind] = max(abs(root_i));
            alac2(i,j,k) = root_i(ind);
        end
    end
end
plot(reshape(abs(alac2),1,[]))
figure,
plot3(alac(1:u,1),alac(1:u,2),alac(1:u,3),'.')

%================End of the code====================================



