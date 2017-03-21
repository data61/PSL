#	title: TrainScript.py
#	author: Yilun He, Data61, CSIRO
#	Python VER 2.7 script

#	Requires sklearn package and its toolchain.

#	This is the python script used to train the generated database
#	Copy this script to the directory where the database is saved

#	Please type "sort Database > SortedDB" in command line in the directory first
#	Then "python TrainScript.py"
import csv
import itertools
import numpy as np
from sklearn.model_selection import cross_val_score
from sklearn.datasets import make_blobs
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import MultiLabelBinarizer
from sklearn.datasets import make_regression
from sklearn.multioutput import MultiOutputRegressor
from sklearn.ensemble import GradientBoostingRegressor
Assert = []
result = []
mlb = MultiLabelBinarizer()
#Find the file SortedDB here. By default in ~/.isabelle directory
with open('SortedDB', 'rb') as csvfile:
	read = csv.reader(csvfile, delimiter = ' ', lineterminator = '\n')
	for row in read:
		if len(row) > 1:
			Assert.append(map(int, (filter(bool, row[0].split(',')))))
			result.append(set([row[1]]))

binary = mlb.fit_transform(result)
current = Assert[0]
counter = 1
X = [Assert[0]]
Y = [binary[0]]
for i in range(1,len(binary)):
	if current != Assert[i]:
		X.append(Assert[i])
		Y[-1] = [float(x)/counter for x in Y[-1]]
		Y.append(binary[i])
		current = Assert[i]
		counter = 1
	else:
		counter = counter + 1;
		Y[-1] = [x + y for x, y in zip(Y[-1], binary[i])]

y = np.array(Y)
T = np.array(list(itertools.product([0,1], repeat = 15)))
result = MultiOutputRegressor(GradientBoostingRegressor(random_state=0)).fit(X,y).predict(T)
Out = zip(T, result)
f = open('recommend','w')
for (t,r) in Out:
	for b in t:
		f.write(str(b)+",")
	f.write(" ")
	recom = zip(r,mlb.classes_)
	sort = sorted(recom, reverse=True)
	for tactuple in sort[0:10]:
		f.write(str(tactuple[1])+ ":" + "%.2f" % tactuple[0])
		f.write(" ")
	f.write("\n")
f.close()
