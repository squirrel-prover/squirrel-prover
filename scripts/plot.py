import sys
import os
import matplotlib.pyplot as plt
import numpy as np
import json
import git

fig, ax = plt.subplots()
plt.xticks(rotation=45, ha='right')
width = 0.35

def bar(stat,col="red",label="unknown",left=True):
    orderedStat = sorted(stat.items(), key=lambda v: v[0])
    xAxis = [v[0] for v in orderedStat]
    yAxis = [v[1] for v in orderedStat]
    x = np.arange(len(xAxis))
    if left:
        shift = x - width/2
    else:
        shift = x + width/2
    ax.bar(shift,yAxis,width,color=col,label=label)
    ax.set_xticks(x, xAxis)

def bar2(stat1,stat2,col="red",label="unknown",left=True):
    orderedStat1 = sorted(stat1.items(), key=lambda v: v[0])
    orderedStat2 = sorted(stat2.items(), key=lambda v: v[0])
    xAxis = [v[0] for v in orderedStat1]
    # diff rate not really relevant for short time running examples…
    # yAxis = [(v2[1]-v1[1])/v1[1] if v1[1] > 0 else 0 for v1,v2 in list(zip(orderedStat1,orderedStat2))]
    yAxis = [(v2[1]-v1[1]) for v1,v2 in list(zip(orderedStat1,orderedStat2))]
    total = 0
    for diff in yAxis:
        total += diff
    mean = total/len(yAxis)
    x = np.arange(len(xAxis))
    ax.bar(x,yAxis,width,color=col,label=label)
    plt.axhline(y=mean, color="green", label="mean diff = "+str(mean)[0:5]+"s")
    ax.set_xticks(x, xAxis)

if len(sys.argv) > 1:
    IN_FILE = sys.argv[1]
    repo = git.Repo(search_parent_directories=True)

    if not os.path.exists(IN_FILE):
        print(IN_FILE + " was not generated, you may want to examinate last.json")
        sys.exit()

    plt.xlabel('file')
    plt.ylabel('time')
    if len(sys.argv) == 3:
        if not os.path.exists(sys.argv[2]):
            print(sys.argv[2] + " was not generated, you may want to examinate last.json malformation")
            sys.exit()
        first = json.load(open(IN_FILE, 'r'))
        last = json.load(open(sys.argv[2], 'r'))
        date1 = os.path.splitext(os.path.basename(IN_FILE))[0]
        bar(first,col="grey",label=date1)
        date = os.path.splitext(os.path.basename(sys.argv[2]))[0]
        if len(repo.head.commit.diff(None))==0:
            label = repo.head.object.hexsha[0:6]
        else:
            label = repo.head.object.hexsha[0:6]+"+"+date+"?"
        bar(last,col="red",label=label,left=False)
        plt.title(date1+"…"+label)
        bar2(first,last,col="blue",label="diff",left=False)
    elif len(sys.argv) == 2:
        dictionary = json.load(open(IN_FILE, 'r'))
        if len(dictionary.keys()) == 0:
            print("No bench found ! type `make bench` to generate one")
            sys.exit()
        elif len(dictionary.keys()) == 1:
            date,stat = list(dictionary.items())[0]
            bar(stat,label=date)
        else:
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
elif len(sys.argv) == 1:
    print("Gathering statistics from _build/squirrel_log/*.json…")
    stats = {}
    for root, dirs, files in os.walk("_build/squirrel_log"):
        for file in files:
            if file.endswith(".json"):
                data = json.load(open(os.path.join(root, file),'r'))
                for k in data.keys():
                    if k in stats:
                        stats[k] = stats[k]+data[k]
                    else:
                        stats[k] = data[k]
                print(os.path.join(root, file)+" OK")
    bar(stats,col="green",label="nb tactic use")
    plt.xlabel('tac')
    plt.ylabel('count')
else:
    print("Too much arguments given…")
    sys.exit()

ax.legend()
plt.grid(True)

plt.show()
