def simple_sort(arr, l):
    if arr[0] > arr[1]:
        t0 = arr[0];
        arr[0] = arr[1];
        arr[1] = t0;
    if arr[1] > arr[2]:
        t1 = arr[1];
        arr[1] = arr[2];
        arr[2] = t1;
    if (arr[0]>arr[1]):
        t2 = arr[0];
        arr[0] = arr[1];
        arr[1] = t2;
    return arr


if __name__ == "__main__":
    arr = [8,3,21]
    l = len(arr)
    res = simple_sort(arr, l)
    print(res)