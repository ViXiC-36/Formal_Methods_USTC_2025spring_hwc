# 1. 兼容性好的 Ubuntu 16.04
FROM ubuntu:16.04
ENV DEBIAN_FRONTEND=noninteractive

# 2. 安装 Java8、Maude、git、wget、tar、unzip、ca-certificates
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      openjdk-8-jdk \
      maude \
      git \
      wget \
      tar \
      unzip \
      ca-certificates && \
    rm -rf /var/lib/apt/lists/*

# 3. 下载并解压 K-legacy v3.5.2 发行包
WORKDIR /opt
RUN wget -q \
      https://github.com/kframework/k-legacy/releases/download/v3.5.2/k-distribution-3.5.2.tar.gz \
      -O k-dist.tar.gz && \
    tar -xzf k-dist.tar.gz && rm k-dist.tar.gz && \
    mv k k-3.5.2    

# 4. 把 K 的 bin 目录加到 PATH
ENV PATH=/opt/k-3.5.2/bin:$PATH

# 5. 设置工作目录到 orc 源码根
WORKDIR /root/orc

# 6. 复制整个 orc/ 目录到镜像中
COPY orc/ /root/orc/

# 7. 编译 Orc-K 的 K 规范
RUN kompile src/orc.k

# 8. 默认用 krun 运行示例程序
ENTRYPOINT ["krun"]
CMD ["test/orcexmp1.orc","-cTL=30","-cV=false"]
