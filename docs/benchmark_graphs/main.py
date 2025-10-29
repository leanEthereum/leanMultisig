import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.ticker import ScalarFormatter, LogLocator
from datetime import datetime, timedelta

# uv run python main.py

N_DAYS_SHOWN = 70

plt.rcParams.update({
    'font.size': 12,           # Base font size
    'axes.titlesize': 14,      # Title font size
    'axes.labelsize': 12,      # X and Y label font size
    'xtick.labelsize': 12,     # X tick label font size
    'ytick.labelsize': 12,     # Y tick label font size
    'legend.fontsize': 12,     # Legend font size
})


def create_duration_graph(data, target=None, target_label=None, title="", y_legend="", file="", label1="Series 1", label2=None, log_scale=False):
    dates = []
    values1 = []
    values2 = []

    # Check if data contains triplets or pairs
    has_second_curve = len(data[0]) == 3 if data else False

    for item in data:
        if has_second_curve:
            day, perf1, perf2 = item
            dates.append(datetime.strptime(day, '%Y-%m-%d'))
            values1.append(perf1)
            values2.append(perf2)
        else:
            day, perf1 = item
            dates.append(datetime.strptime(day, '%Y-%m-%d'))
            values1.append(perf1)

    color = '#2E86AB'
    color2 = '#A23B72'  # Different color for second curve

    _, ax = plt.subplots(figsize=(10, 6))

    # Filter out None values for first curve
    dates1_filtered = [d for d, v in zip(dates, values1) if v is not None]
    values1_filtered = [v for v in values1 if v is not None]

    ax.plot(dates1_filtered, values1_filtered, marker='o', linewidth=2,
            markersize=7, color=color, label=label1)

    # Plot second curve if it exists
    if has_second_curve and label2 is not None:
        # Filter out None values for second curve
        dates2_filtered = [d for d, v in zip(dates, values2) if v is not None]
        values2_filtered = [v for v in values2 if v is not None]

        ax.plot(dates2_filtered, values2_filtered, marker='s', linewidth=2,
                markersize=7, color=color2, label=label2)
        all_values = values1_filtered + values2_filtered
    else:
        all_values = values1_filtered

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
        ax.axhline(y=target, color=color, linestyle='--',
                   linewidth=2, label=target_label)

    ax.set_ylabel(y_legend, fontsize=12)
    ax.set_title(title, fontsize=16, pad=15)
    ax.grid(True, alpha=0.3, which='both')  # Grid for both major and minor ticks
    ax.legend()

    # Set log scale if requested
    if log_scale:
        ax.set_yscale('log')
        
        # Set locators for major and minor ticks
        ax.yaxis.set_major_locator(LogLocator(base=10.0, numticks=15))
        ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=range(1, 10), numticks=100))
        
        # Format labels
        ax.yaxis.set_major_formatter(ScalarFormatter())
        ax.yaxis.set_minor_formatter(ScalarFormatter())
        ax.yaxis.get_major_formatter().set_scientific(False)
        ax.yaxis.get_minor_formatter().set_scientific(False)
        
        # Show minor tick labels
        ax.tick_params(axis='y', which='minor', labelsize=10)
    else:
        # Adjust y-limit to accommodate both curves (only for linear scale)
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
            ('2025-08-27', 85000, None),
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
        label1="i9-12900H",
        label2="mac m4 max",
        log_scale=False
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 2.7, None),
            ('2025-09-07', 1.4, None),
            ('2025-09-09', 1.32, None),
            ('2025-09-10', 0.970, None),
            ('2025-09-14', 0.825, None),
            ('2025-09-28', 0.725, None),
            ('2025-10-01', 0.685, None),
            ('2025-10-03', 0.647, None),
            ('2025-10-12', 0.569, None),
            ('2025-10-13', 0.521, None),
            ('2025-10-18', 0.411, 0.320),
            ('2025-10-27', 0.425, 0.330),
        ],
        target=0.1,
        target_label="Target (0.1 s)",
        title="Recursive WHIR opening (log scale)",
        y_legend="Proving time (s)",
        file="recursive_whir_opening",
        label1="i9-12900H",
        label2="mac m4 max",
        log_scale=True
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 35, None),
            ('2025-09-02', 37, None),
            ('2025-09-03', 53, None),
            ('2025-09-09', 62, None),
            ('2025-09-10', 76, None),
            ('2025-09-14', 107, None),
            ('2025-09-28', 137, None),
            ('2025-10-01', 172, None),
            ('2025-10-03', 177, None),
            ('2025-10-07', 193, None),
            ('2025-10-12', 214, None),
            ('2025-10-13', 234, None),
            ('2025-10-18', 255, 465),
            ('2025-10-27', 314, 555),
        ],
        target=1000,
        target_label="Target (1000 XMSS/s)",
        title="number of XMSS aggregated / s",
        y_legend="",
        file="xmss_aggregated",
        label1="i9-12900H",
        label2="mac m4 max"
    )

    create_duration_graph(
        data=[
            ('2025-08-27', 14.2 / 0.92, None),
            ('2025-09-02', 13.5 / 0.82, None),
            ('2025-09-03', 9.4 / 0.82, None),
            ('2025-09-09', 8.02 / 0.72, None),
            ('2025-09-10', 6.53 / 0.72, None),
            ('2025-09-14', 4.65 / 0.72, None),
            ('2025-09-28', 3.63 / 0.63, None),
            ('2025-10-01', 2.9 / 0.42, None),
            ('2025-10-03', 2.81 / 0.42, None),
            ('2025-10-07', 2.59 / 0.42, None),
            ('2025-10-12', 2.33 / 0.40, None),
            ('2025-10-13', 2.13 / 0.38, None),
            ('2025-10-18', 1.96 / 0.37, 1.07 / 0.12),
            ('2025-10-27', (610_000 / 157) / 314, (1_250_000 / 157) / 555),
            ('2025-10-29', (650_000 / 157) / 314, (1_300_000 / 157) / 555),
        ],
        target=2,
        target_label="Target (2x)",
        title="XMSS aggregated: zkVM overhead vs raw Poseidons",
        y_legend="",
        file="xmss_aggregated_overhead",
        label1="i9-12900H",
        label2="mac m4 max"
    )