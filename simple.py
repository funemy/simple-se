def simple_sort(arr, l):
    if arr[0] > arr[1]:
        t = arr[0];
        arr[0] = arr[1];
        arr[1] = t;
    if arr[1] > arr[2]:
        t = arr[1];
        arr[1] = arr[2];
        arr[2] = t;
    if (arr[0]>arr[1]):
        t = arr[0];
        arr[0] = arr[1];
        arr[1] = t;
    return arr


if __name__ == "__main__":
    arr = [8,3,21]
    l = len(arr)
    res = simple_sort(arr, l)
    print(res)