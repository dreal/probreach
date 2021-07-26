# def generate_next_state(state):
# 	unit = random.choice(state)
# 	if unit in transitions.keys():
# 		next_state = tuple([random.choice(transitions[unit]) if unit == x else x for x in state])
# 		return next_state
# 	else:
# 		return tuple()		

# def get_unit_name(unit):
# 	return unit.split('_')[0]

import random
import itertools
import numpy as np

P1 = ['P1_on', 'P1_off', 'P1_stuck_on', 'P1_stuck_off']
P2 = ['P2_on', 'P2_off', 'P2_stuck_on', 'P2_stuck_off']
V = ['V_on', 'V_off', 'V_stuck_on', 'V_stuck_off']

transitions = {'P1_on':['P1_off', 'P1_stuck_on', 'P1_stuck_off'], \
				'P1_off':['P1_on', 'P1_stuck_on', 'P1_stuck_off'], \
				'P2_on':['P2_off', 'P2_stuck_on', 'P2_stuck_off'], \
				'P2_off':['P2_on', 'P2_stuck_on', 'P2_stuck_off'], \
				'V_on':['V_off', 'V_stuck_on', 'V_stuck_off'], \
				'V_off':['V_on', 'V_stuck_on', 'V_stuck_off']}

faulty_trans = {'P1_on':['P1_stuck_on', 'P1_stuck_off'], \
				'P1_off':['P1_stuck_on', 'P1_stuck_off'], \
				'P2_on':['P2_stuck_on', 'P2_stuck_off'], \
				'P2_off':['P2_stuck_on', 'P2_stuck_off'], \
				'V_on':['V_stuck_on', 'V_stuck_off'], \
				'V_off':['V_stuck_on', 'V_stuck_off']}

increase = {'P1_off':'P1_on', \
			'P2_off':'P2_on', \
			'V_on':'V_off'}

decrease = {'P1_on':'P1_off', \
			'P2_on':'P2_off', \
			'V_off':'V_on'}

inflow_values = {'P1_on':1, 'P1_off':0, 'P1_stuck_on':1, 'P1_stuck_off':0, \
				'P2_on':1, 'P2_off':0, 'P2_stuck_on':1, 'P2_stuck_off':0, \
				'V_on':-1, 'V_off':0, 'V_stuck_on':-1, 'V_stuck_off':0}

stuck_states = {'P1_stuck_on', 'P1_stuck_off', \
				'P2_stuck_on', 'P2_stuck_off', \
				'V_stuck_on', 'V_stuck_off'}							

state_space = list(itertools.product(P1,P2,V))
state_space = dict(zip(state_space, range(1, len(state_space)+1)))

time_limit = 20
unsat = 0
need_to_check = 0
iter_num = 10000
for i in range(0,iter_num):
	P1_fault = np.random.exponential(438)
	P2_fault = np.random.exponential(350)
	V_fault = np.random.exponential(640)
	# print('P1 fault: ', P1_fault)
	# print('P2 fault: ', P2_fault)
	# print('V fault: ', V_fault)
	if max([P1_fault, P2_fault, V_fault]) > time_limit:
		unsat += 1
	else:
		need_to_check += 1	

print('UNSATs:', unsat, '; ', 100*(unsat/iter_num), '%')
print('Need to check:', need_to_check, '; ', 100*(need_to_check/iter_num), '%')



for state in state_space:
	print("// current state: ", state)
	inflow_val = sum([inflow_values[unit] for unit in state])
	print("{")
	print("mode ", state_space[state], ";")
	print("time: [0, 20-tau];")
	print("invt:")
	print("(tau_P1 <= 20);")
	print("(tau_P2 <= 20);")
	print("(tau_V <= 20);")
	print("(tau_P1_rep <= tau_P1_rep_var);")
	print("(tau_P2_rep <= tau_P2_rep_var);")
	print("(tau_V_rep <= tau_V_rep_var);")
	print("(tau <= 20);")
	print("flow: ")
	print("d/dt[H] = ", inflow_val, "*q;")
	# if inflow_val < 0: print("state: ", state, "; inflow = ", inflow_val)
	print("d/dt[tau_P1] = 1;")
	print("d/dt[tau_P2] = 1;")
	print("d/dt[tau_V] = 1;")
	if state[0] in ("P1_stuck_on", "P1_stuck_off"):
		print("d/dt[tau_P1_rep] = 1;")
	else:
		print("d/dt[tau_P1_rep] = 0;")
	if state[1] in ("P2_stuck_on", "P2_stuck_off"):
		print("d/dt[tau_P2_rep] = 1;")
	else:
		print("d/dt[tau_P2_rep] = 0;")
	if state[2] in ("V_stuck_on", "V_stuck_off"):
		print("d/dt[tau_V_rep] = 1;")
	else:
		print("d/dt[tau_V_rep] = 0;")
	print("d/dt[tau] = 1;")
	print("jump:")
	faulty_components = []
	# faulty transitions
	for unit in state:
		if unit in faulty_trans:
			unit_name = unit.split('_')[0]
			faulty_components.append(unit_name)
	# print("// faulty components: ", set(faulty_components))		

	# faulty transitions
	for unit in state:
		if unit in faulty_trans:
			for next_unit in faulty_trans[unit]:
				next_state = tuple([next_unit if unit == x else x for x in state])
				# print("Possible trans: ", next_unit, "; next state: ", next_state, "; mode: ", state_space[next_state])
				next_id = state_space[next_state]
				unit_name = unit.split('_')[0]
				next_state = next_unit.split('_')[-1]
				guard = ("(and (tau_"+unit_name+">=tau_fault_"+unit_name+")"+"(tau_"+unit_name+"<=tau_fault_"+unit_name+")")
				# guard = ("(and (tau_"+unit_name+"="+next_unit+")")
				for f in faulty_components:
					if f != unit_name:
						guard += ("(tau_"+unit_name+"<tau_fault_"+f+")")
				if(next_state == 'on'):		
					guard += ("(choice_"+unit_name+"=-1)")
				else:
					guard += ("(choice_"+unit_name+"=1)")	
				guard += ")"
				print(guard, " ==> @", next_id, "(and (tau_P1' = tau_P1) (tau_P2' = tau_P2) (tau_V' = tau_V));")

	next_state = []
	for unit in state:
		next_state.append(increase[unit] if unit in increase else unit)
	next_state = tuple(next_state)
	if next_state != state:
		next_id = state_space[next_state]
		print("(H = H_low) ==> @", next_id, "(tau' = tau);")

	next_state = []
	for unit in state:
		next_state.append(decrease[unit] if unit in decrease else unit)
	next_state = tuple(next_state)
	if next_state != state:
		next_id = state_space[next_state]
		print("(H = H_high) ==> @", next_id, "(tau' = tau);")

	print("}")
	print()
	print()




