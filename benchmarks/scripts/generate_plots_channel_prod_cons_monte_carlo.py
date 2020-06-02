# Please, run this script from the root folder of this module.

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import locale
from matplotlib.ticker import FormatStrFormatter
from matplotlib.backends.backend_pdf import PdfPages

input_file = "out/results_channel_prod_cons_montecarlo.csv"
output_file = "out/channel-prod-cons-monte-carlo.pdf"

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['#EA00FF', '#F7A3FF', '#238199', '#2DA6C4', '#139100', '#1CD100', '#fb6a4a', '#fcae91', '#62629E', '#8585D6', '#2B2B2B', '#858585', '#BABA00', '#FFFF00']

def next_colour():
    for colour in colours:
        yield colour

def next_marker():
    for marker in markers:
        yield marker

def draw(data, ax_arr):
    if isinstance(ax_arr, np.ndarray):
        flatten_ax_arr = ax_arr.flatten()
    else:
        flatten_ax_arr = [ax_arr]
    for ax in flatten_ax_arr:
        ax.set_xscale('log', basex=2)
        ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
        ax.grid(linewidth='0.5', color='lightgray')
        ax.set_ylabel("transfer avg time, ns")
        ax.set_xlabel('threads')
        ax.set_xticks(data.threads.unique())

    i = 0
    for dispatcher_type in data.dispatcherType.unique():
        colour_gen = next_colour()
        marker_gen = next_marker()
        flatten_ax_arr[i].set_title("{} dispatcher".format(dispatcher_type))

        for channel in data.channel.unique():
            for with_select in data.withSelect.unique():
                gen_colour = next(colour_gen)
                gen_marker = next(marker_gen)
                res = data[(data.dispatcherType == dispatcher_type) & (data.withSelect == with_select) & (data.channel == channel)]
                flatten_ax_arr[i].errorbar(x = res.threads, y = res.result, yerr=res.error,
                                           label="channel = {} {}".format(channel, "[with select]" if with_select else ""), 
                                           color=gen_colour, marker=gen_marker, capsize=5)
        i += 1

with PdfPages(output_file) as pdf:
    langlocale = locale.getdefaultlocale()[0]
    locale.setlocale(locale.LC_ALL, langlocale)
    dp = locale.localeconv()['decimal_point']
    data = pd.read_csv(input_file, sep=",", decimal=dp)
    plt.rcParams.update({'font.size': 15})
    plots = len(data.dispatcherType.unique())
    fig, ax_arr = plt.subplots(nrows=plots, ncols=1, figsize=(15, plots * 10))
    draw(data, ax_arr)
    if isinstance(ax_arr, np.ndarray): ax = ax_arr[0]
    else: ax = ax_arr
    lines, labels = ax.get_legend_handles_labels()
    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=2, frameon=False, borderaxespad=2, prop={'size': 15})

    plt.tight_layout(pad=11, w_pad=2, h_pad=4)
    pdf.savefig(bbox_inches='tight')