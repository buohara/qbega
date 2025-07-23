RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    flex \
    bison \
    git \
    gdb \
    valgrind \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /qbe

CMD ["/bin/bash"]