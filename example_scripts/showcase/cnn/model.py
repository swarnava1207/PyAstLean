import math


class CNN:
    """A tiny convolutional neural network, trained from scratch with hand-written backprop.

    Architecture (every dimension is fixed so the Lean structure stays concrete):
        8x8 grayscale image
          -> 2x2 valid convolution (single kernel)  -> 7x7 feature map
          -> ReLU
          -> flatten                                 -> 49-vector
          -> dense (49 -> 1) + sigmoid               -> probability
    The task is a 2-class problem on real MNIST digits downsampled to 8x8: the digit "1"
    (label 1) vs the digit "0" (label 0). Parameters, forward pass, gradients and the SGD
    update all live inside the class -- and this whole class is what gets transpiled to Lean.
    """

    def __init__(self):
        # Explicit annotations pin the Lean structure field types.
        self.kernel: list[list[float]] = [[0.1, -0.2], [0.15, 0.05]]
        self.dense_w: list[float] = [
            0.05, -0.05, 0.05, -0.05, 0.05, -0.05, 0.05,
            -0.05, 0.05, -0.05, 0.05, -0.05, 0.05, -0.05,
            0.05, -0.05, 0.05, -0.05, 0.05, -0.05, 0.05,
            -0.05, 0.05, -0.05, 0.05, -0.05, 0.05, -0.05,
            0.05, -0.05, 0.05, -0.05, 0.05, -0.05, 0.05,
            -0.05, 0.05, -0.05, 0.05, -0.05, 0.05, -0.05,
            0.05, -0.05, 0.05, -0.05, 0.05, -0.05, 0.05,
        ]
        self.dense_b: float = 0.0

    def sigmoid(self, x: float) -> float:
        return 1.0 / (1.0 + math.exp(-x))

    def conv(self, img: list[list[float]]) -> list[list[float]]:
        # Valid 2x2 convolution over an 8x8 image -> 7x7 feature map.
        out = []
        for i in range(7):
            row = []
            for j in range(7):
                s = 0.0
                for a in range(2):
                    for b in range(2):
                        s = s + img[i + a][j + b] * self.kernel[a][b]
                row.append(s)
            out.append(row)
        return out

    def relu2d(self, fm: list[list[float]]) -> list[list[float]]:
        out = []
        for i in range(7):
            row = []
            for j in range(7):
                v = fm[i][j]
                if v < 0.0:
                    v = 0.0
                row.append(v)
            out.append(row)
        return out

    def flatten(self, fm: list[list[float]]) -> list[float]:
        out = []
        for i in range(7):
            for j in range(7):
                out.append(fm[i][j])
        return out

    def forward(self, img: list[list[float]]) -> float:
        c = self.conv(img)
        r = self.relu2d(c)
        f = self.flatten(r)
        z = self.dense_b
        for k in range(49):
            z = z + f[k] * self.dense_w[k]
        return self.sigmoid(z)

    def predict(self, img: list[list[float]]) -> int:
        if self.forward(img) >= 0.5:
            return 1
        return 0

    def train(self, images: list[list[list[float]]], labels: list[int], epochs: int, lr: float):
        # Stochastic gradient descent with binary cross-entropy (the sigmoid+BCE gradient on
        # the logit reduces to `pred - target`). Each step rebuilds the parameter lists rather
        # than mutating them in place, matching the transpiler's value-semantics model.
        for e in range(epochs):
            for n in range(len(images)):
                img = images[n]
                target = float(labels[n])

                # Forward pass, keeping the intermediates we need for backprop.
                c = self.conv(img)
                r = self.relu2d(c)
                f = self.flatten(r)
                z = self.dense_b
                for k in range(49):
                    z = z + f[k] * self.dense_w[k]
                pred = self.sigmoid(z)

                d_logit = pred - target

                # Gradient w.r.t. the flattened features (uses the pre-update dense weights).
                dflat = []
                for k in range(49):
                    dflat.append(d_logit * self.dense_w[k])

                # Update the dense layer.
                new_w = []
                for k in range(49):
                    new_w.append(self.dense_w[k] - lr * d_logit * f[k])
                self.dense_w = new_w
                self.dense_b = self.dense_b - lr * d_logit

                # Backprop through ReLU, reshaping the 49-vector grad to the 7x7 map.
                dconv = [
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                ]
                idx = 0
                for i in range(7):
                    for j in range(7):
                        g = dflat[idx]
                        if r[i][j] <= 0.0:
                            g = 0.0
                        dconv[i][j] = g
                        idx = idx + 1

                # Backprop into the convolution kernel and update it.
                new_kernel = [[0.0, 0.0], [0.0, 0.0]]
                for a in range(2):
                    for b in range(2):
                        gk = 0.0
                        for i in range(7):
                            for j in range(7):
                                gk = gk + dconv[i][j] * img[i + a][j + b]
                        new_kernel[a][b] = self.kernel[a][b] - lr * gk
                self.kernel = new_kernel


def main():
    # The dataset arrives on stdin as plain floats -- the showcase decodes the PNGs in
    # Python and streams the pixels here, so this file (the part Lean transpiles) never
    # hardcodes any image. Layout:
    #     line 1            : number of images N
    #     then per image    : the label (0/1), followed by 64 pixel values (8x8, row-major)
    n = int(input())
    images = []
    labels = []
    for idx in range(n):
        label = int(input())
        labels.append(label)
        img = []
        for r in range(8):
            row = []
            for c in range(8):
                px = float(input())
                row.append(px)
            img.append(row)
        images.append(img)

    cnn = CNN()
    cnn.train(images, labels, 250, 0.4)

    correct = 0
    for k in range(n):
        p = cnn.predict(images[k])
        print("pred", k, p)
        if p == labels[k]:
            correct = correct + 1
    print("accuracy", correct, n)


if __name__ == "__main__":
    main()
