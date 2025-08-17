# Stage 1: Build Python dependencies
FROM python:3.10-slim as builder

# Install core build dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        build-essential \
        libjpeg-dev \
        zlib1g-dev \
        libpng-dev \
        libfreetype6-dev \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app
COPY requirements.txt .

# Install Python packages
RUN pip install --user --no-cache-dir -r requirements.txt

# Stage 2: Final runtime image with FFmpeg and other media dependencies
FROM python:3.10-slim

# Install core dependencies including ffmpeg, libgomp1 for Pillow, and fonts for MoviePy/Pillow
# Also adding ttf-mscorefonts-installer to get 'arial.ttf'
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        ffmpeg \
        libsm6 \
        libxext6 \
        libgomp1 \
        fonts-dejavu-core \
        fonts-freefont-ttf \
        fonts-noto-cjk \
        ttf-mscorefonts-installer \
    && rm -rf /var/lib/apt/lists/*

# Copy installed Python packages from the builder stage
COPY --from=builder /root/.local /root/.local

# Set environment variables for ffmpeg and other tools
ENV PATH="/root/.local/bin:${PATH}"
ENV IMAGEIO_FFMPEG_EXE="/usr/bin/ffmpeg"
ENV FONTCONFIG_PATH="/etc/fonts"

# Set working directory for the application
WORKDIR /app

# Copy project files into the working directory
COPY . .

# Expose the port for the health check server
EXPOSE 8080

# Command to run your bot
CMD ["python3", "main.py"]
