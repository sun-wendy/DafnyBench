import numpy as np
import plotly.express as px
import plotly.graph_objs as go


def get_success_rate_vs_num_attempts(model):
    csv_file_path = f"../results_summary/{model}_results.csv"
    with open(csv_file_path, 'r') as f:
        lines = f.readlines()
    
    num_success_vs_num_attempts = {}
    for i in range(0, 11):
        num_success_vs_num_attempts[i] = []
    for line in lines[1:]:
        line = line.strip().split(',')
        for i in range(0, 11):
            if line[2] == 'failed':
                num_success_vs_num_attempts[i].append(0)
            else:
                if int(line[2]) <= i:
                    num_success_vs_num_attempts[i].append(1)
                else:
                    num_success_vs_num_attempts[i].append(0)
    
    num_attempts_mean, num_attempts_std = {}, {}
    for i in range(0, 11):
        num_attempts_mean[i] = np.mean(num_success_vs_num_attempts[i])
        num_attempts_std[i] = np.std(num_success_vs_num_attempts[i]) / np.sqrt(len(num_success_vs_num_attempts[i]))
    return num_attempts_mean, num_attempts_std


def match_model_testfile_metadata(model):
    results_file = f"../results_summary/{model}_results.csv"
    metadata_file = "../../DafnyBench/metadata/ground_truth_metadata.csv"

    test_results = []
    num_char, num_hint_char, num_lemma = [], [], []

    with open(results_file, 'r') as f:
        lines = f.readlines()
        for line in lines[1:]:
            line = line.strip().split(',')
            indicator = 0 if line[2] == 'failed' else 1
            test_results.append(indicator)
    
    with open(metadata_file, 'r') as f1:
        metadata_lines = f1.readlines()
        for metadata_line in metadata_lines[1:]:
            metadata_line = metadata_line.strip().split(',')
            num_char.append(int(metadata_line[4]))
            num_hint_char.append(int(metadata_line[5]))
            num_lemma.append(int(metadata_line[6]))
    
    return test_results, num_char, num_hint_char, num_lemma


def bin_metadata(model_test_results, num_char_list, num_hint_char_list, num_lemma_list):
    # Define bin edges using quantiles to ensure each bin has approximately the same number of elements

    epsilon = 1e-10
    num_char_list_noisy = num_char_list + epsilon * np.random.randn(len(num_char_list))
    num_hint_char_list_noisy = num_hint_char_list + epsilon * np.random.randn(len(num_hint_char_list))
    num_lemma_list_noisy = num_lemma_list + epsilon * np.random.randn(len(num_lemma_list))

    bin_edges_num_char = np.quantile(num_char_list, np.linspace(0, 1, 11))
    bin_edges_num_hint_char = np.quantile(num_hint_char_list, np.linspace(0, 1, 11))
    bin_edges_num_lemma = np.quantile(num_lemma_list, np.linspace(0, 1, 11))
    
    bin_num_char = {(bin_edges_num_char[i], (bin_edges_num_char[i]+bin_edges_num_char[i+1])/2.0, bin_edges_num_char[i+1]): [] for i in range(10)}
    bin_num_hint_char = {(bin_edges_num_hint_char[i], (bin_edges_num_hint_char[i]+bin_edges_num_hint_char[i+1])/2.0, bin_edges_num_hint_char[i+1]): [] for i in range(10)}
    bin_num_lemma = {(bin_edges_num_lemma[i], (bin_edges_num_lemma[i]+bin_edges_num_lemma[i+1])/2.0, bin_edges_num_lemma[i+1]): [] for i in range(10)}

    # Function to determine which bin an element belongs to
    def find_bin(value, bin_edges):
        for i in range(10):
            if bin_edges[i] <= value < bin_edges[i+1]:
                return (bin_edges[i], (bin_edges[i] + bin_edges[i+1]) / 2.0, bin_edges[i+1])
        return (bin_edges[9], (bin_edges[9] + bin_edges[10]) / 2.0, bin_edges[10])

    # Assign values to bins
    for success_indicator, num_char, num_hint_char, num_lemma in zip(model_test_results, num_char_list, num_hint_char_list, num_lemma_list):
        bin_num_char[find_bin(num_char, bin_edges_num_char)].append(success_indicator)
        bin_num_hint_char[find_bin(num_hint_char, bin_edges_num_hint_char)].append(success_indicator)
        bin_num_lemma[find_bin(num_lemma, bin_edges_num_lemma)].append(success_indicator)

    return bin_num_char, bin_num_hint_char, bin_num_lemma


def get_bin_width_mean_error(model):
    test_results, num_char, num_hint_char, num_lemma = match_model_testfile_metadata(model)
    bin_num_char, bin_num_hint_char, bin_num_lemma = bin_metadata(test_results, num_char, num_hint_char, num_lemma)

    num_programs_list, mean_list, error_list = [], [], []
    for bin_list in [bin_num_char, bin_num_hint_char, bin_num_lemma]:
        num_programs = {key: len(val) for key, val in bin_list.items()}
        bin_mean = {key: np.mean(val) for key, val in bin_list.items()}
        bin_error = {key: np.std(val) / np.sqrt(len(val)) for key, val in bin_list.items()}
        num_programs_list.append(num_programs)
        mean_list.append(bin_mean)
        error_list.append(bin_error)
    
    return num_programs_list, mean_list, error_list


def scatter_num_attempts(error_y_mode=None, **kwargs):
    # Code taken from: https://stackoverflow.com/questions/69587547/continuous-error-band-with-plotly-express-in-python
    ERROR_MODES = {'bar','band','bars','bands',None}

    if error_y_mode not in ERROR_MODES:
        raise ValueError(f"'error_y_mode' must be one of {ERROR_MODES}, received {repr(error_y_mode)}.")
    
    if error_y_mode in {'bar','bars',None}:
        fig = px.line(**kwargs)
    
    elif error_y_mode in {'band','bands'}:
        if 'error_y' not in kwargs:
            raise ValueError(f"If you provide argument 'error_y_mode' you must also provide 'error_y'.")
        fig_with_error_bars = px.line(**kwargs)
        fig = px.line(**{arg: val for arg,val in kwargs.items() if arg != 'error_y'})
        for data in fig_with_error_bars.data:
            x = list(data['x'])
            y_upper = list(data['y'] + data['error_y']['array'])
            y_lower = list(data['y'] - data['error_y']['array'] if data['error_y']['arrayminus'] is None else data['y'] - data['error_y']['arrayminus'])
            color = f"rgba({tuple(int(data['line']['color'].lstrip('#')[i:i+2], 16) for i in (0, 2, 4))},.3)".replace('((','(').replace('),',',').replace(' ','')
            fig.add_trace(
                go.Scatter(
                    x = x+x[::-1],
                    y = y_upper+y_lower[::-1],
                    fill = 'toself',
                    fillcolor = color,
                    line = dict(
                        color = 'rgba(255,255,255,0)'
                    ),
                    hoverinfo = "skip",
                    showlegend = False,
                    legendgroup = data['legendgroup'],
                    xaxis = data['xaxis'],
                    yaxis = data['yaxis'],
                )
            )
        
        fig.update_layout(yaxis_tickformat=',.0%', legend_title=None, width=900, height=600, font=dict(size = 30))
        fig.update_yaxes(range=[0, 0.8])
        reordered_data = []
        for i in range(int(len(fig.data) / 2)):
            reordered_data.append(fig.data[i+int(len(fig.data)/2)])
            reordered_data.append(fig.data[i])
        fig.data = tuple(reordered_data)
    
    return fig


def scatter_with_error_bands(bin_endpoints, error_y_mode=None, **kwargs):
    # Code taken from: https://stackoverflow.com/questions/69587547/continuous-error-band-with-plotly-express-in-python
    ERROR_MODES = {'bar','band','bars','bands',None}

    if error_y_mode not in ERROR_MODES:
        raise ValueError(f"'error_y_mode' must be one of {ERROR_MODES}, received {repr(error_y_mode)}.")
    
    if error_y_mode in {'bar','bars',None}:
        fig = px.line(**kwargs)
    
    elif error_y_mode in {'band','bands'}:
        if 'error_y' not in kwargs:
            raise ValueError(f"If you provide argument 'error_y_mode' you must also provide 'error_y'.")
        fig_with_error_bars = px.line(**kwargs)
        fig = px.line(**{arg: val for arg,val in kwargs.items() if arg != 'error_y'})
        for data in fig_with_error_bars.data:
            x = list(data['x'])
            y_upper = list(data['y'] + data['error_y']['array'])
            y_lower = list(data['y'] - data['error_y']['array'] if data['error_y']['arrayminus'] is None else data['y'] - data['error_y']['arrayminus'])
            color = f"rgba({tuple(int(data['line']['color'].lstrip('#')[i:i+2], 16) for i in (0, 2, 4))},.3)".replace('((','(').replace('),',',').replace(' ','')
            fig.add_trace(
                go.Scatter(
                    x = x+x[::-1],
                    y = y_upper+y_lower[::-1],
                    fill = 'toself',
                    fillcolor = color,
                    line = dict(
                        color = 'rgba(255,255,255,0)'
                    ),
                    hoverinfo = "skip",
                    showlegend = False,
                    legendgroup = data['legendgroup'],
                    xaxis = data['xaxis'],
                    yaxis = data['yaxis'],
                )
            )
        
        fig.update_layout(yaxis_tickformat=',.0%', legend_title=None, width=900, height=600, font=dict(size = 30))
        fig.update_xaxes(type='log', showgrid=True, dtick=1, minor=dict(ticks="inside", ticklen=6, showgrid=False))
        fig.update_yaxes(range=[0, 1])

        # Add vertical lines to mark bin boundaries
        for endpoint in bin_endpoints:
            fig.add_vline(x=endpoint, line_width=1, line_dash="dash", line_color="blue")
        
        reordered_data = []
        for i in range(int(len(fig.data) / 2)):
            reordered_data.append(fig.data[i+int(len(fig.data)/2)])
            reordered_data.append(fig.data[i])
        fig.data = tuple(reordered_data)
    
    return fig
