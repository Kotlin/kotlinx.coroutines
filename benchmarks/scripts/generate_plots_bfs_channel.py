import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

inputFile = "resultsBfs.csv"
outputFile = "bfs_channel.png"

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']

def next_colour():
    for colour in colours:
        yield colour

def next_marker():
    for marker in markers:
        yield marker

def draw(data, plt):
    plt.xscale('log', basex=2)
    plt.gca().xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    plt.grid(linewidth='0.5', color='lightgray')
    plt.ylabel('time (ms)')
    plt.xlabel('coroutines')
    plt.xticks(data.coroutines.unique())

    colour_gen = next_colour()
    marker_gen = next_marker()
    for graphName in data.graphName.unique():
        gen_colour = next(colour_gen)
        gen_marker = next(marker_gen)
        res_parallel = data[(data.graphName == graphName) & (data.coroutines != 0)]
        plt.plot(res_parallel.coroutines, res_parallel.executionTimeAvgMs, label="graphName={}".format(graphName), color=gen_colour, marker=gen_marker)
        res_sequential = data[(data.graphName == graphName) & (data.coroutines == 0)]
        res_sequential = pd.concat([res_sequential.executionTimeAvgMs]*(len(res_parallel.coroutines)))
        plt.plot(res_parallel.coroutines, res_sequential, linestyle='--',label="graphName={}-sequential".format(graphName), color=gen_colour)

data = pd.read_table(inputFile, sep=",")
plt.figure(figsize=(20, 15))
draw(data, plt)
plt.legend(loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})
plt.tight_layout(pad=12, w_pad=2, h_pad=1)
plt.savefig(outputFile, bbox_inches='tight')