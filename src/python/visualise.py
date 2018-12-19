import pandas as pd
import matplotlib.pyplot as plt
import sys

# the last element is the full path to the file
data = pd.read_json(sys.argv[-1])
# itterating through all trajectories
for i in range(0,len(data['trajectories'])):
	df = pd.DataFrame(data['trajectories'][i])
	# checking if any variables for plotting are specified
	if(len(sys.argv) <= 2):
		df.plot(x='.global_time', title='Trajectory '+str(i+1))
	else:
		# setting the grid
		fig, axes = plt.subplots(nrows=len(sys.argv)-2, ncols=1)
		fig.suptitle('Trajectory '+str(i+1))
		# iterating through the specified variables
		for j in range(1, len(sys.argv)-1):
			if(sys.argv[j] == '--all'):
				df.plot(x='.global_time', ax=axes[j-1])
			else:
				df.plot(x='.global_time', y=sys.argv[j], ax=axes[j-1])

plt.show()