import pandas as pd
import random
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.colors import ListedColormap
from matplotlib.backends.backend_pdf import PdfPages

inputFile = "resultsBfs.csv"
outputFile = "plotsBfs.png"

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

    colourGen = next_colour()
    markerGen = next_marker()
    for graphName in data.graphName.unique():
        genColour = next(colourGen)
        genMarker = next(markerGen)
        resParallel = data[(data.graphName == graphName) & (data.coroutines != 0)]
        plt.plot(resParallel.coroutines, resParallel.executionTimeAvgMs, label="graphName={}".format(graphName), color=genColour, marker=genMarker)
        resSequential = data[(data.graphName == graphName) & (data.coroutines == 0)]
        resSequential = pd.concat([resSequential.executionTimeAvgMs]*(len(resParallel.coroutines)))
        plt.plot(resParallel.coroutines, resSequential, linestyle='--',label="graphName={}-sequential".format(graphName), color=genColour)

def genFile():
    data = pd.read_table(inputFile, sep=",")
    plt.figure(figsize=(20, 15))
    draw(data, plt)
    plt.legend(loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})
    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
    plt.savefig(outputFile, bbox_inches='tight')

genFile()