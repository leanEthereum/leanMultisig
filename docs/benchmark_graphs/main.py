import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime, timedelta

# uv run python main.py

N_DAYS_SHOWN = 30

plt.rcParams.update({
    'font.size': 12,           # Base font size
    'axes.titlesize': 16,      # Title font size
    'axes.labelsize': 12,      # X and Y label font size
    'xtick.labelsize': 12,     # X tick label font size
    'ytick.labelsize': 12,     # Y tick label font size
    'legend.fontsize': 12,     # Legend font size
})


def create_duration_graph(data, target=None, target_label=None, title="", y_legend="", file="", label1="Series 1", label2=None):
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

    _, ax = plt.subplots(figsize=(8, 4.8))
    ax.plot(dates, values1, marker='o', linewidth=2,
            markersize=7, color=color, label=label1)

    # Plot second curve if it exists
    if has_second_curve and label2 is not None:
        ax.plot(dates, values2, marker='s', linewidth=2,
                markersize=7, color=color2, label=label2)
        all_values = values1 + values2
    else:
        all_values = values1

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

    ax.set_ylabel(y_legend)
    ax.set_title(title, pad=15)
    ax.grid(True, alpha=0.3)
    ax.legend()

    # Adjust y-limit to accommodate both curves
    max_value = max(all_values)
    if target is not None:
        max_value = max(max_value, target)
    ax.set_ylim(0, max_value * 1.1)

    plt.tight_layout()
    plt.savefig(f'graphs/{file}.svg', format='svg', bbox_inches='tight')


if __name__ == "__main__":

    create_duration_graph(
        data=[
            ('2025-10-26', 230_000, 620_000),
            ('2025-10-27', 610_000, 1_250_000),
        ],
        target=1_500_000,
        target_label="Target (1.5M Poseidon2 / s)",
        title="Raw Poseidon2",
        y_legend="Poseidons proven / s",
        file="raw_poseidons",
        label1="i9-12900H",
        label2="mac m4 max"
    )

    create_duration_graph(
        data=[
            ('2025-10-26', 0.411, 0.320),
            ('2025-10-27', 0.425, 0.330),
        ],
        target=0.1,
        target_label="Target (0.1 s)",
        title="Recursive WHIR opening",
        y_legend="Proving time (s)",
        file="recursive_whir_opening",
        label1="i9-12900H",
        label2="mac m4 max"
    )

    create_duration_graph(
        data=[
            ('2025-10-26', 255, 465),
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
