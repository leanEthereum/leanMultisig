import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.ticker import ScalarFormatter, LogLocator
from datetime import datetime, timedelta

# uv run python main.py

N_DAYS_SHOWN = 130

plt.rcParams.update({
    'font.size': 12,           # Base font size
    'axes.titlesize': 14,      # Title font size
    'axes.labelsize': 12,      # X and Y label font size
    'xtick.labelsize': 12,     # X tick label font size
    'ytick.labelsize': 12,     # Y tick label font size
    'legend.fontsize': 12,     # Legend font size
})


def create_duration_graph(data, target=None, target_label=None, title="", y_legend="", file="", labels=None, log_scale=False):
    if labels is None:
        labels = ["Series 1"]

    # Number of curves based on tuple length
    num_curves = len(data[0]) - 1 if data else 1  # -1 for the date

    dates = []
    values = [[] for _ in range(num_curves)]

    for item in data:
        dates.append(datetime.strptime(item[0], '%Y-%m-%d'))
        for i in range(num_curves):
            values[i].append(item[i + 1])

    colors = ['#2E86AB', '#A23B72', '#28A745', '#FF6F00', '#6A1B9A']
    markers = ['o', 's', '^', 'D', 'v']

    _, ax = plt.subplots(figsize=(10, 6))

    all_values = []

    for i in range(num_curves):
        if i >= len(labels):
            break  # No label provided for this curve

        # Filter out None values
        dates_filtered = [d for d, v in zip(dates, values[i]) if v is not None]
        values_filtered = [v for v in values[i] if v is not None]

        if values_filtered:  # Only plot if there's data
            ax.plot(dates_filtered, values_filtered, 
                    marker=markers[i % len(markers)], 
                    linewidth=2,
                    markersize=7, 
                    color=colors[i % len(colors)], 
                    label=labels[i])
            all_values.extend(values_filtered)

    min_date = min(dates)
    max_date = max(dates)
    date_range = max_date - min_date
    if date_range < timedelta(days=N_DAYS_SHOWN):
        max_date = min_date + timedelta(days=N_DAYS_SHOWN)
    ax.set_xlim(min_date - timedelta(days=1), max_date + timedelta(days=1))

    ax.xaxis.set_major_locator(mdates.WeekdayLocator(interval=1))
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%m/%d'))

    plt.setp(ax.xaxis.get_majorticklabels(), rotation=50, ha='right')

    if target is not None and target_label is not None:
        ax.axhline(y=target, color='#555555', linestyle='--',
                   linewidth=2, label=target_label)

    ax.set_ylabel(y_legend, fontsize=12)
    ax.set_title(title, fontsize=16, pad=15)
    ax.grid(True, alpha=0.3, which='both')
    ax.legend()

    if log_scale:
        ax.set_yscale('log')
        
        ax.yaxis.set_major_locator(LogLocator(base=10.0, numticks=15))
        ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=range(1, 10), numticks=100))
        
        ax.yaxis.set_major_formatter(ScalarFormatter())
        ax.yaxis.set_minor_formatter(ScalarFormatter())
        ax.yaxis.get_major_formatter().set_scientific(False)
        ax.yaxis.get_minor_formatter().set_scientific(False)
        
        ax.tick_params(axis='y', which='minor', labelsize=10)
    else:
        if all_values:
            max_value = max(all_values)
            if target is not None:
                max_value = max(max_value, target)
            ax.set_ylim(0, max_value * 1.1)

    plt.tight_layout()
    plt.savefig(f'graphs/{file}.svg', format='svg', bbox_inches='tight')


if __name__ == "__main__":

    create_duration_graph(
        data=[
            ('2025-08-27', 85000, None,),
            ('2025-08-30', 95000, None),
            ('2025-09-09', 108000, None),
            ('2025-09-14', 108000, None),
            ('2025-09-28', 125000, None),
            ('2025-10-01', 185000, None),
            ('2025-10-12', 195000, None),
            ('2025-10-13', 205000, None),
            ('2025-10-18', 210000, 620_000),
            ('2025-10-27', 610_000, 1_250_000),
            ('2025-10-29', 650_000, 1_300_000),
        ],
        target=1_500_000,
        target_label="Target (1.5M Poseidon2 / s)",
        title="Raw Poseidon2",
        y_legend="Poseidons proven / s",
        file="raw_poseidons",
        labels=["i9-12900H", "mac m4 max"],
        log_scale=False
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 2.7, None, None),
            ('2025-09-07', 1.4, None, None),
            ('2025-09-09', 1.32, None, None),
            ('2025-09-10', 0.970, None, None),
            ('2025-09-14', 0.825, None, None),
            ('2025-09-28', 0.725, None, None),
            ('2025-10-01', 0.685, None, None),
            ('2025-10-03', 0.647, None, None),
            ('2025-10-12', 0.569, None, None),
            ('2025-10-13', 0.521, None, None),
            ('2025-10-18', 0.411, 0.320, None),
            ('2025-10-27', 0.425, 0.330, None),
            ('2025-11-15', 0.417, 0.330, None),
            ('2025-12-04', None, 0.097, 0.130),
        ],
        target=0.1,
        target_label="Target (0.1 s)",
        title="Recursive WHIR opening (log scale)",
        y_legend="Proving time (s)",
        file="recursive_whir_opening",
        labels=["i9-12900H", "mac m4 max", "mac m4 max | lean-vm-simple"],
        log_scale=True
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 35, None, None),
            ('2025-09-02', 37, None, None),
            ('2025-09-03', 53, None, None),
            ('2025-09-09', 62, None, None),
            ('2025-09-10', 76, None, None),
            ('2025-09-14', 107, None, None),
            ('2025-09-28', 137, None, None),
            ('2025-10-01', 172, None, None),
            ('2025-10-03', 177, None, None),
            ('2025-10-07', 193, None, None),
            ('2025-10-12', 214, None, None),
            ('2025-10-13', 234, None, None),
            ('2025-10-18', 255, 465, None),
            ('2025-10-27', 314, 555, None),
            ('2025-11-02', 350, 660, None),
            ('2025-11-15', 380, 720, None),
            ('2025-12-04', None, 940, 755),
        ],
        target=1000,
        target_label="Target (1000 XMSS/s)",
        title="number of XMSS aggregated / s",
        y_legend="",
        file="xmss_aggregated",
        labels=["i9-12900H", "mac m4 max", "mac m4 max | lean-vm-simple"]
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 14.2 / 0.92, None, None),
            ('2025-09-02', 13.5 / 0.82, None, None),
            ('2025-09-03', 9.4 / 0.82, None, None),
            ('2025-09-09', 8.02 / 0.72, None, None),
            ('2025-09-10', 6.53 / 0.72, None, None),
            ('2025-09-14', 4.65 / 0.72, None, None),
            ('2025-09-28', 3.63 / 0.63, None, None),
            ('2025-10-01', 2.9 / 0.42, None, None),
            ('2025-10-03', 2.81 / 0.42, None, None),
            ('2025-10-07', 2.59 / 0.42, None, None),
            ('2025-10-12', 2.33 / 0.40, None, None),
            ('2025-10-13', 2.13 / 0.38, None, None),
            ('2025-10-18', 1.96 / 0.37, 1.07 / 0.12, None),
            ('2025-10-27', (610_000 / 157) / 314, (1_250_000 / 157) / 555, None),
            ('2025-10-29', (650_000 / 157) / 314, (1_300_000 / 157) / 555, None),
            ('2025-11-02', (650_000 / 157) / 350, (1_300_000 / 157) / 660, None),
            ('2025-11-15', (650_000 / 157) / 380, (1_300_000 / 157) / 720, None),
            ('2025-12-04', None, (1_300_000 / 157) / 940, (1_300_000 / 157) / 755),
        ],
        target=2,
        target_label="Target (2x)",
        title="XMSS aggregated: zkVM overhead vs raw Poseidons",
        y_legend="",
        file="xmss_aggregated_overhead",
        labels=["i9-12900H", "mac m4 max", "mac m4 max | lean-vm-simple"]
    )