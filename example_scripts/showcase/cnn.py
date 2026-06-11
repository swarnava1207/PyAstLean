import math


class CNN:
    """A tiny convolutional neural network, trained from scratch with hand-written backprop.

    Architecture (all dimensions fixed for clarity):
        3x3 input image
          -> 2x2 convolution (single kernel)   -> 2x2 feature map
          -> ReLU
          -> flatten                            -> 4-vector
          -> dense (4 -> 1) + sigmoid           -> probability
    The task is a 2-class problem: vertical-stripe images (label 1) vs horizontal-stripe
    images (label 0). Everything — parameters, forward pass, gradients, and the SGD update —
    lives inside the class.
    """

    def __init__(self):
        # Explicit annotations pin the Lean structure field types.
        self.kernel: list[list[float]] = [[0.1, -0.2], [0.15, 0.05]]
        self.dense_w: list[float] = [0.1, -0.1, 0.2, -0.2]
        self.dense_b: float = 0.0

    def sigmoid(self, x: float) -> float:
        return 1.0 / (1.0 + math.exp(-x))

    def conv(self, img: list[list[float]]) -> list[list[float]]:
        # Valid 2x2 convolution over a 3x3 image -> 2x2 feature map.
        out = []
        for i in range(2):
            row = []
            for j in range(2):
                s = 0.0
                for a in range(2):
                    for b in range(2):
                        s = s + img[i + a][j + b] * self.kernel[a][b]
                row.append(s)
            out.append(row)
        return out

    def relu2d(self, fm: list[list[float]]) -> list[list[float]]:
        out = []
        for i in range(2):
            row = []
            for j in range(2):
                v = fm[i][j]
                if v < 0.0:
                    v = 0.0
                row.append(v)
            out.append(row)
        return out

    def flatten(self, fm: list[list[float]]) -> list[float]:
        return [fm[0][0], fm[0][1], fm[1][0], fm[1][1]]

    def forward(self, img: list[list[float]]) -> float:
        c = self.conv(img)
        r = self.relu2d(c)
        f = self.flatten(r)
        z = self.dense_b
        for k in range(4):
            z = z + f[k] * self.dense_w[k]
        return self.sigmoid(z)

    def predict(self, img: list[list[float]]) -> int:
        if self.forward(img) >= 0.5:
            return 1
        return 0

    def train(self, images: list[list[list[float]]], labels: list[int], epochs: int, lr: float):
        # Stochastic gradient descent with binary cross-entropy (the sigmoid+BCE gradient on the
        # logit reduces to `pred - target`). Each step rebuilds the parameter lists rather than
        # mutating them in place, matching the transpiler's value-semantics model.
        for e in range(epochs):
            for n in range(len(images)):
                img = images[n]
                target = float(labels[n])

                # Forward pass, keeping the intermediates we need for backprop.
                c = self.conv(img)
                r = self.relu2d(c)
                f = self.flatten(r)
                z = self.dense_b
                for k in range(4):
                    z = z + f[k] * self.dense_w[k]
                pred = self.sigmoid(z)

                d_logit = pred - target

                # Gradient w.r.t. the flattened features (uses the pre-update dense weights).
                dflat = []
                for k in range(4):
                    dflat.append(d_logit * self.dense_w[k])

                # Update the dense layer.
                new_w = []
                for k in range(4):
                    new_w.append(self.dense_w[k] - lr * d_logit * f[k])
                self.dense_w = new_w
                self.dense_b = self.dense_b - lr * d_logit

                # Backprop through ReLU, reshaping the 4-vector grad to the 2x2 map.
                dconv = [[0.0, 0.0], [0.0, 0.0]]
                idx = 0
                for i in range(2):
                    for j in range(2):
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
                        for i in range(2):
                            for j in range(2):
                                gk = gk + dconv[i][j] * img[i + a][j + b]
                        new_kernel[a][b] = self.kernel[a][b] - lr * gk
                self.kernel = new_kernel


def main():
    # Vertical-stripe images are class 1; horizontal-stripe images are class 0.
    images = [
        [[1.0, 0.0, 0.0], [1.0, 0.0, 0.0], [1.0, 0.0, 0.0]],
        [[0.0, 1.0, 0.0], [0.0, 1.0, 0.0], [0.0, 1.0, 0.0]],
        [[0.0, 0.0, 1.0], [0.0, 0.0, 1.0], [0.0, 0.0, 1.0]],
        [[1.0, 1.0, 1.0], [0.0, 0.0, 0.0], [0.0, 0.0, 0.0]],
        [[0.0, 0.0, 0.0], [1.0, 1.0, 1.0], [0.0, 0.0, 0.0]],
        [[0.0, 0.0, 0.0], [0.0, 0.0, 0.0], [1.0, 1.0, 1.0]],
    ]
    labels = [1, 1, 1, 0, 0, 0]

    cnn = CNN()
    cnn.train(images, labels, 400, 0.5)

    correct = 0
    for n in range(len(images)):
        if cnn.predict(images[n]) == labels[n]:
            correct = correct + 1

    print("accuracy:", correct, "/", len(images))
    print("vertical   sample -> class", cnn.predict(images[0]))
    print("horizontal sample -> class", cnn.predict(images[3]))


if __name__ == "__main__":
    main()
