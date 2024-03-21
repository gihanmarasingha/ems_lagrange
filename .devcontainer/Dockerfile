# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.245.2/containers/debian/.devcontainer/base.Dockerfile

# [Choice] Debian version (use bullseye on local arm64/Apple Silicon): bullseye, buster
FROM leanprovercommunity/lean:debian

# ** [Optional] Uncomment this section to install additional packages. **
# RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
#     && apt-get -y install --no-install-recommends <your-package-list-here>

RUN ssh -o StrictHostKeyChecking=no github.com || true

# Install LaTeX
# RUN sudo apt-get -q update && \
#     sudo apt-get install -yq texlive-latex-extra latexmk && \ 
#     sudo rm -rf /var/lib/apt/lists/*
#
# RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain stable --no-modify-path -y
# ENV PATH="$HOME/.elan/bin:${PATH}"