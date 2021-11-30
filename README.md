# A Short Introduction to Coq

This is a repository with the Jupyter notebook used for the Coq workshop in the FoS course.

You can run these notebooks online, here are the links:

- [advanced](https://mybinder.org/v2/git/https%3A%2F%2Fc4science.ch%2Fdiffusion%2F9452%2Fcoq-project.git/master?filepath=advanced.ipynb)
- [advanced\_full](https://mybinder.org/v2/git/https%3A%2F%2Fc4science.ch%2Fdiffusion%2F9452%2Fcoq-project.git/master?filepath=advanced\_full.ipynb)
- [demo](https://mybinder.org/v2/git/https%3A%2F%2Fc4science.ch%2Fdiffusion%2F9452%2Fcoq-project.git/master?filepath=demo.ipynb)

## Running it locally

You will need to install Coq, Jupyter and the `coq_jupyter` kernel.
You can do that more-or-less as follows:

```shell
brew install coq # or something similar for your OS
pip install --user coq_jupyter==1.5.0
python -m coq_jupyter.install
```

Depending on your system, you may also need to run:

```shell
pip install --user notebook
```

## Run

```shell
jupyter notebook
```

Note: using `jupyter lab` does not work correctly. Use the notebook version.
