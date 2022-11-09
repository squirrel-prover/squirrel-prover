from sys import argv
import os
import matplotlib.pyplot as plt
import numpy as np
import json

IN_FILE = argv[1]

fig, ax = plt.subplots()
plt.xticks(rotation=45, ha='right')
width = 0.35

def bar(stat,col="red",label="unknown",left=True):
    xAxis = [key for key, value in stat.items()]
    yAxis = [value for key, value in stat.items()]
    x = np.arange(len(xAxis))
    if left:
        ax.bar(x - width/2,yAxis,width,color=col,label=os.path.basename(IN_FILE))
    else:
        ax.bar(x + width/2,yAxis,width,color=col,label=label)
    ax.set_xticks(x, xAxis)

if len(argv)>2:
    print(argv)
    first = json.load(open(IN_FILE, 'r'))
    last = json.load(open(argv[2], 'r'))
    bar(first,col="grey",label=os.path.basename(IN_FILE))
    bar(last,col="red",label="last bench",left=False)

else:
    dictionary = json.load(open(IN_FILE, 'r'))
    rate = 1/len(dictionary.keys())
    means = {}
    dates = list(dictionary.keys())
    print(dates[-1])

    # Collect previous values and compute means
    for date in dates[:-1]:
        for file,value in dictionary[date].items():
            if file in means.keys():
                means[file] = means[file]+value
            else:
                means[file] = value

    for file,value in means.items():
        means[file] = means[file]/len(dates[:-1])

    bar(means,col="grey",label="mean prev/*")
    bar(dictionary[dates[-1]],col="red",label=dates[-1],left=False)

ax.legend()
plt.xlabel('file')
plt.ylabel('time')
plt.grid(True)

plt.show()
