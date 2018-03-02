# Build the tool

For building the entire tool chain for Units, just run below command in
directory `units-inference`:

```bash
# cd units-inference
./dependency-setup.sh
```

# Running Units on sci-corpus

## Dependencies & prerequisites 

To run driver script `run-units-on-corpus.py`, you need first to install below
packages:

- pyYaml: `pip install pyyaml`

The driver script need python version higher than `2.7.10`.

### Regarding DLJC

We currently use a customized version of [do-like-
javac](https://github.com/pascaliUWat/do-like-javac.git). In `dependency-
setup.sh` we download this version of DLJC in the parent dir of units-
inference.

You also need to install Lithium for the test case minimizer:
https://github.com/pascaliUWat/do-like-javac/blob/master/README_testminimizer.md


## Running the tool
To run units-inference on sci-corpus, just run following command:

```bash
# cd units-inference
python run-units-on-corpus.py
```

This script would first fetching the projects defined in `projects.yml` from
[opprop-benchmarks](https://github.com/opprop-benchmarks) into `units-
inference/corpus`, then running Units on this corpus.

After this script finished, you can check the `logs/infer.log` under each
project directory to see the tool running log, and `logs/infer_result_*.jaif`
are the inference output of onology on each project.

You can also run `analyze-corpus.sh` to extract high level summaries for each
corpus.

### Regarding the sci-corpus

You may notice currently there were some projects has been commented out in
`projects.yml`, i.e. we are running on a sub-set of sci-corpus. Most of those
projects cannot compile (have basic java compile issues), with two of them we
still have problems to infer results on them, and currently are working on
fixing them.
