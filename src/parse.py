import numpy as np
import h5py
import argparse

def format_list(lst):
    ret = ",".join(["\"{x}\"".format(x=x) for x in lst])
    return "[" + ret + "]"


def floatList2str(data):
    def float2str(v):
        if v == float("-inf"):
            return "negf (divf 1.0 0.0)"
        elif v < 0.0:
            return "negf {}".format(-v)
        else:
            return "{}".format(v)
    lst = map(float2str, data)
    s = ",".join(["{x}".format(x=x) for x in lst])
    return "[" + s + "]"

def floatListOfList2str(data):
    return "[" + ",".join(map(floatList2str, data)) + "]"


def read_model(model_path):
    with h5py.File(model_path, 'r') as f:
        normal_high = f['Parameters']['Normalization'].attrs['HighClip']
        normal_low = f['Parameters']['Normalization'].attrs['LowClip']
        signal_n = f['Parameters']['Normalization'].attrs['SignalLevels']
        signal_n = f['Tables']['ObservationProbabilities'].shape[0]
        observation = f['Tables']['ObservationProbabilities'][:]
        transition = f['Tables']['TransitionProbabilities'][:]
        kmer = (
            np.log2(f['Tables']['ObservationProbabilities'].shape[1])/2).astype(int)
        D = f['Tables']['DurationProbabilities'].shape[0]
        tail_factor = f['Tables']['DurationProbabilities'].attrs['TailFactor']
        duration = f['Tables']['DurationProbabilities'][:]
        duration[-1] = duration[-1]*(1-tail_factor)
        middlek = int(kmer//2)

    return {'signalLevels': signal_n,
            'observationProbabilities': floatListOfList2str(np.log(observation).tolist()),
            'transitionProbabilities': floatListOfList2str(np.log(transition).tolist()),
            'k': kmer,
            'dMax': D,
            'tailFactor': tail_factor,
            'duration': floatList2str(np.log(duration).tolist())}


def write_model(output_file, model):
    with open(output_file, 'w') as out:
        out.write(
            """
        {{ signalLevels = {signalLevels}
        , observationProbabilities = {observationProbabilities}
        , transitionProbabilities = {transitionProbabilities}
        , k = {k}
        , dMax = {dMax}
        , tailFactor = {tailFactor}
        , duration = {duration}
        }}
        """
            .format(signalLevels=model['signalLevels'],
                    observationProbabilities=model['observationProbabilities'],
                    transitionProbabilities=model['transitionProbabilities'],
                    k=model['k'],
                    dMax=model['dMax'],
                    tailFactor=model['tailFactor'],
                    duration=model['duration'])
        )


def read_signal(signal_path):
    with h5py.File(signal_path, 'r') as f:
        keys = list(f.keys())
        signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]
        return {'keys': keys, 'signals': signals}

def write_signal(output_file, signals):
    with open(output_file, 'w') as out:
        out.write(
            """
            {{ keys = {keys}
            , signals = {signals}
            }}
            """
            .format(keys=format_list(signals['keys'][0:1]),
                    signals=signals['signals'][0:1])
        )


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Convert Trellis fast 5 files into text files.')
    parser.add_argument(
        '--model', help='filename of input model in fast 5 format')
    parser.add_argument('--output-model', help='filename of output model')
    parser.add_argument(
        '--signal', help='filename of input signal in fast 5 format')
    parser.add_argument('--output-signal', help='filename of output signal')

    args = parser.parse_args()

    model = read_model(args.model)
    write_model(args.output_model, model)

    signals = read_signal(args.signal)
    write_signal(args.output_signal, signals)
