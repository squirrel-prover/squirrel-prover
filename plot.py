from sys import argv
import matplotlib.pyplot as plt
import json

IN_FILE = argv[1]

dictionary = json.load(open(IN_FILE, 'r'))
rate = 1/len(dictionary.keys())
count = 0
fig, ax = plt.subplots()
means = {}
dates = list(dictionary.keys())

print(dates[-1])

plt.xticks(rotation=45, ha='right')

# Collect previous values and compute means
for date in dates[:-1]:
    for file,value in dictionary[date].items():
        if file in means.keys():
            means[file] = means[file]+value
        else:
            means[file] = value

for file,value in means.items():
    means[file] = means[file]/len(dates[:-1])

xAxis = [key for key in means.keys()]
yAxis = [value for value in means.values()]
ax.bar(xAxis,yAxis,0.35,color="grey",alpha=0.5)

stat = dictionary[dates[-1]]
xAxis = [key for key, value in stat.items()]
yAxis = [value for key, value in stat.items()]
ax.bar(xAxis,yAxis,0.35,color="red",alpha=0.5)

plt.xlabel('file')
plt.ylabel('time')
plt.grid(True)

# Display all
# for date in dictionary.keys():
#     stat = dictionary[date]
#     xAxis = [key for key, value in stat.items()]
#     yAxis = [value for key, value in stat.items()]
#     # col = plt.colors.to_rgba(100,100,100)
#     col = (1,count*rate,count*rate)
#     # plt.plot(xAxis,yAxis, color=col, marker='o')

#     ax.bar(xAxis,yAxis,0.35,color=col)

#     count = count + 1

plt.show()
