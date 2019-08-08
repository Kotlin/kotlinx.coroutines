import pandas as pd
import random
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.colors import ListedColormap
from matplotlib.backends.backend_pdf import PdfPages

inputFile = "results.csv"
outputFile = "plots.pdf"

def nextColour():
    colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']

    for colour in colours:
        yield colour

def nextMarker():
    markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']

    for marker in markers:
        yield marker

def draw(data, benchMode, avgWork, users, maxFriends, sentAx, receivedAx):
    sentAx.set_xscale('log', basex=2)
    sentAx.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    sentAx.grid(linewidth='0.5', color='lightgray')
    sentAx.set_ylabel('msgSent / ms')
    sentAx.set_xlabel('threads')
    sentAx.set_xticks(data.threads.unique())

    receivedAx.set_xscale('log', basex=2)
    receivedAx.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    receivedAx.grid(linewidth='0.5', color='lightgray')
    receivedAx.set_ylabel('msgReceived / ms')
    receivedAx.set_xlabel('threads')
    receivedAx.set_xticks(data.threads.unique())

    colourGen = nextColour()
    markerGen = nextMarker()
    for channelType in data.channelType.unique():
        for dispatcherType in data.dispatcherType.unique():
            genColour = next(colourGen)
            genMarker = next(markerGen)
            res = data[(data.benchmarkMode == benchMode) & (data.averageWork == avgWork) & (data.userCount == users) & (data.maxFriendsPercentage == maxFriends) & (data.channelType == channelType) & (data.dispatcherType == dispatcherType)]
            sentAx.plot(res.threads, res.avgSentMessages, label="channel={},dispatcher={}".format(channelType, dispatcherType), color=genColour)
            sentAx.errorbar(x=res.threads, y=res.avgSentMessages, yerr=res.stdSentMessages, solid_capstyle='projecting', capsize=5)
            receivedAx.plot(res.threads, res.avgReceivedMessages, label="channel={},dispatcher={}".format(channelType, dispatcherType), color=genColour)
            receivedAx.errorbar(x=res.threads, y=res.avgReceivedMessages, yerr=res.stdReceivedMessages, solid_capstyle='projecting', capsize=5)

def genFile(pdf):
    data = pd.read_table(inputFile, sep=",")
    for benchMode in data.benchmarkMode.unique():
        for avgWork in data.averageWork.unique():
            for users in data.userCount.unique():
                for maxFriends in data.maxFriendsPercentage.unique():
                    fig, (ax1, ax2) = plt.subplots(nrows=2, ncols=1, figsize=(20, 20))
                    draw(data, benchMode, avgWork, users, maxFriends, ax1, ax2)
                    lines, labels = ax1.get_legend_handles_labels()
                    fig.suptitle("benchMode={},avgWork={},users={},maxFriends={}".format(benchMode, avgWork, users, maxFriends), fontsize=12, y=1)
                    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})

                    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
                    pdf.savefig(bbox_inches='tight')

with PdfPages(outputFile) as pdf:
    genFile(pdf)