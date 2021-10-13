# Example notebooks using z3tracer

## Installing Jupyter notebook and Rust kernel
* Install JupyterLab and Jupyter Notebook using the following commands:
```
pip install jupyterlab
pip install notebook
```
If these commands don't work or if you want to install using `conda` instead, 
see the documentation of [Jupyter Software](https://jupyter.org/install) for the most up-to-date installation instructions.

* Install the Rust kernel in Jupyter notebooks on Mac OS by running the following commands:
```
cargo install evcxr_jupyter
evcxr_jupyter --install
``` 
If these commands don't work or if you want to install on a different platform, 
see the documentation of [EvCxR Jupyter Kernel](https://github.com/google/evcxr/blob/master/evcxr_jupyter/README.md) 
for the most up-to-date installation instructions.

## Running the example notebooks

* Run `jupyter lab z3tracer/notebooks` command from root directory of this repository and open one example file.

* Execute each cell step by step (for instance using SHIFT+RET or the play button at the top panel). NOTE: compiling and loading crates may take some time.

* Examples based on [plotly](https://github.com/igiagkiozis/plotly) may require [additional installation steps](https://igiagkiozis.github.io/plotly/content/fundamentals/jupyter_support.html)
  to make Javascript libraries available to Jupyter notebooks. Eventually, it should look like
  [this](https://nbviewer.jupyter.org/github/facebookincubator/smt2utils/blob/main/z3tracer/notebooks/example_plotly.ipynb).
